-- Jakub Kuszneruk jk320790

module Misc where

import Absshl
import ErrM

--type Ident = String
--  deriving Eq

data VarState = Vst[(Typ, Ident, Constraint)]
  deriving Show
data RefState = Rst[(Typ, Ident, Ident)]
  deriving Show
data ArrState = Ast[(Typ, Ident, [Constraint])]
  deriving Show
data FunState = Fst[(Typ, Ident, [FArg], Blk, Integer)]
  deriving Show
data BufState = Bst[Constraint]
  deriving Show
data RetValue = Return Constraint | NotRet
  deriving Show

data State = St(VarState, RefState, ArrState, FunState, BufState, State, RetValue, Integer, Integer, Integer) | BottomState
  deriving Show
{-
 - VarState - stored variables
 - RefState - stored references (mapping id to id)
 - FunState - stored functions
 - BufState - informations to print at the end of the program
 - State - parent state (state 1lvl below us)
 - RetValue -
 - Integer - state lvl (how deep we are, useful for static binding - function remember how deep was it defined)
 - Integer - lvl on which current function was declared
 - Integer - lvl when function was invoked
-}



getRetValue :: State -> Err Constraint
getRetValue (St (_, _, _, _, _, _, NotRet, _, _, _)) = Ok $ Eint 0
getRetValue (St (_, _, _, _, _, _, Return ret, _, _, _)) = Ok ret

setRetValue :: State -> RetValue -> State
setRetValue (St (vst, rst, ast, fst, bst, st, _, clvl, flvl, ilvl)) ret =
  St(vst, rst, ast, fst, bst, st, ret, clvl, flvl, ilvl)

-- set proper function declaration state lvl and function invoke state lvl in state
setFlvl :: State -> Integer -> Integer -> State
setFlvl (St (vst, rst, ast, fst, bst, st, ret, clvl, _, _)) flvl ilvl =
  St(vst, rst, ast, fst, bst, st, ret, clvl, flvl, ilvl)

-- helper function
findVarId id found (t, i, c)
  | i == id = (t, i, c)
  | otherwise = found


getRefTranslation :: State -> Ident -> Integer -> Either (Ident, Integer) Ident
getRefTranslation BottomState id _ = Right id
getRefTranslation (St (_, Rst rst, _, _, _, stc, _, clvl, _, _)) id top_ilvl =
--  if (clvl >= top_ilvl) && (any (\(_, i, _) -> id == i) rst)
  if (any (\(_, i, _) -> id == i) rst)
    then Left (((\(_, _, c) -> c)(foldl (findVarId id) (head rst) rst)), clvl)
    else getRefTranslation stc id top_ilvl

lookvarR :: State -> Ident -> Integer -> Integer -> Err Constraint
lookvarR BottomState id _ _ = Bad $ "no such varbiable: " ++ (show id)
lookvarR (St (Vst vst, _, _, _, _, stc, _, clvl, _, _)) id top_flvl top_ilvl =
    if (clvl <= top_flvl || clvl > top_ilvl) && (any (\(_, i, _) -> id == i) vst)
      then Ok ((\(_, _, c) -> c)(foldl (findVarId id) (head vst) vst))
      else lookvarR stc id top_flvl top_ilvl

lookvar :: State -> Ident -> Err Constraint
lookvar state@(St (Vst vst, Rst rst, _, _, _, stc, _, clvl, top_flvl, top_ilvl)) id = do
  case getRefTranslation state id top_ilvl of
    Left (translated_id, var_lvl) -> lookvarR state translated_id var_lvl (clvl+99)
    Right translated_id -> lookvarR state translated_id top_flvl top_ilvl

getType :: Constraint -> Err Typ
getType con =
  case con of
  Eint _ -> Ok TInt
  Ebool _ -> Ok TBool
  Estring _ -> Ok TString

updateR :: State -> Ident -> Constraint -> Integer -> Integer -> Err State
updateR BottomState id con top_flvl top_ilvl =
  case getType con of
  Ok t -> Bad $ "No such identifier: " ++ (show id) ++ " of type: " ++ (show t) ++ " to update."
  otherwise -> Bad "Unknown error during resolving variable type"
updateR (St (Vst vst, Rst rst, Ast ast,Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) id con top_flvl top_ilvl =
  let { updateV el@(t, i, c)
        | i == id = (t, i, con)
        | otherwise = el }
    in
    if ((clvl <= top_flvl || clvl > top_ilvl) && any (\(t, i, _) -> id == i && (getType con == Ok t)) vst)
      then
        Ok $ St(Vst (map updateV vst), Rst rst, Ast ast, Fst fst, Bst bst, stc,
          NotRet, clvl, flvl, ilvl)
      else do
        updated_state <- updateR stc id con top_flvl top_ilvl;
        Ok $ St(Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, updated_state,
          NotRet, clvl, flvl, ilvl)

update :: State -> Ident -> Constraint -> Err State
update state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, t_flvl, t_ilvl)) id con = do
  case getRefTranslation state id t_ilvl of
    Left (translated_id, var_lvl) -> updateR state translated_id con var_lvl (clvl+99)
    Right translated_id -> updateR state translated_id con t_flvl t_ilvl

declare :: State -> Typ -> Ident -> Constraint -> Err State
declare state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) typ id con =
  if (any (\(_, i, _) -> id == i) vst) || (any (\(_, i, _) -> id == i) ast)
    then Bad "Identifier is declared in this scope"
      else
        Ok (
          St(Vst ((typ, id, con):vst), Rst rst, Ast ast, Fst fst, Bst bst, stc,
            NotRet, clvl, flvl, ilvl))

-- declare for references
refer :: State -> Typ -> Ident -> Typ -> Ident -> Err State
refer state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) typ1 id1 typ2 id2 =
  if typ1 /= typ2 then Bad "Type mismatch"
    else
    if (any (\(_, i, _) -> id1 == i) rst) then Bad "Reference is declared in this scope"
      else if any (\(t, i, _) -> id2 == i && (typ1 == t)) vst
        then Bad "No such variable to map"
        else Ok (
          St(Vst vst, Rst ((typ1, id1, id2):rst), Ast ast, Fst fst, Bst bst, stc,
            NotRet, clvl, flvl, ilvl))

declareF :: State -> Typ -> Ident -> [FArg] -> Blk -> Err State
declareF state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, st, _, clvl, flvl, ilvl)) typ id args blk =
  if (any (\(_, i, _, _, _) -> id == i) fst)
    then Bad "Function with such name is defined"
    else Ok (
      St(Vst vst, Rst rst, Ast ast, Fst ((typ,  id,  args,  blk,  clvl):fst), Bst bst,
        st, NotRet, clvl, flvl, ilvl))
declareF BottomState _ _ _ _ = Bad "declareF programming error"

create_def_arr arr siz val =
  if siz == 0 then arr
    else create_def_arr (val:arr) (siz - 1) val


lookArrR :: State -> Ident -> Integer -> Integer -> Integer -> Err Constraint
lookArrR BottomState id ix _ _ = Bad $ "no such array: " ++ (show id) ++ " " ++ (show ix)
lookArrR (St (_, _, Ast ast, _, _, stc, _, clvl, _, _)) id ix top_flvl top_ilvl =
    if (clvl <= top_flvl || clvl > top_ilvl) && (any (\(_, i, _) -> id == i) ast)
      then Ok ((\(_, _, c) -> c !! (fromIntegral ix))(foldl (findVarId id) (head ast) ast))
      else lookArrR stc id ix top_flvl top_ilvl

lookArr :: State -> Ident -> Integer -> Err Constraint
lookArr state@(St (_, _, Ast ast, _, _, stc, _, clvl, top_flvl, top_ilvl)) id ix = do
  case getRefTranslation state id top_ilvl of
    Left (translated_id, var_lvl) -> lookArrR state translated_id ix var_lvl (clvl+99)
    Right translated_id -> lookArrR state translated_id ix top_flvl top_ilvl

updateIx [] arr ix con count = reverse arr
updateIx (h:t) arr ix con count =
  if ix == count then updateIx t (con:arr) ix con (count + 1)
    else updateIx t (h:arr) ix con (count + 1)
updateArrR :: State -> Ident -> Integer -> Constraint -> Integer -> Integer -> Err State
updateArrR BottomState id ix con top_flvl top_ilvl =
  case getType con of
  Ok t -> Bad $ "No such identifier: " ++ (show id) ++ " of type: " ++ (show t) ++ " to update."
  otherwise -> Bad "Unknown error during resolving variable type"
updateArrR (St (Vst vst, Rst rst, Ast ast,Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) id ix con top_flvl top_ilvl =
  let { updateA el@(t, i, c)
        | i == id = (t, i, updateIx c [] ix con 0)
        | otherwise = el }
    in
    if ((clvl <= top_flvl || clvl > top_ilvl) && any (\(t, i, _) -> id == i && (getType con == Ok t)) ast)
      then
        Ok $ St(Vst vst, Rst rst, Ast (map updateA ast), Fst fst, Bst bst, stc,
          NotRet, clvl, flvl, ilvl)
      else do
        updated_state <- updateArrR stc id ix con top_flvl top_ilvl;
        Ok $ St(Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, updated_state,
          NotRet, clvl, flvl, ilvl)

updateArr :: State -> Ident -> Integer -> Constraint -> Err State
updateArr state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, t_flvl, t_ilvl)) id ix con =
  case getRefTranslation state id t_ilvl of
    Left (translated_id, var_lvl) -> updateArrR state translated_id ix con var_lvl (clvl+99)
    Right translated_id -> updateArrR state translated_id ix con t_flvl t_ilvl

declareA :: State -> Typ -> Ident -> Integer -> Constraint -> Err State
declareA state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, st, _, clvl, flvl, ilvl)) typ id siz val = do
  let def_arr = create_def_arr [] siz val
    in
      if (any (\(_, i, _) -> id == i) vst) || (any (\(_, i, _) -> id == i) ast)
        then Bad "Such id is already defined in this scope"
        else Ok (
          St(Vst vst, Rst rst, Ast ((typ, id, def_arr):ast), Fst fst, Bst bst, st,
            NotRet, clvl, flvl, ilvl))
declareA BottomState _ _ _ _ = Bad "declareF programming error"

-- helper function
findFunId id found (t, i, a, c, dlvl)
  | i == id = (t, i, a, c, dlvl)
  | otherwise = found

getFunR :: State -> Ident -> Integer -> Integer -> Err (Typ, Ident, [FArg], Blk, Integer)
getFunR BottomState id _ _ = Bad $ "function:" ++ (show id) ++ "doesn't exist"
getFunR (St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, _, _)) id top_flvl top_ilvl =
  if (clvl <= top_flvl || clvl > top_ilvl) && (any (\(_, i, _, _, _) -> id == i) fst)
    then Ok $ foldl (findFunId id) (head fst) fst
    else getFunR stc id top_flvl top_ilvl

getFun :: State -> Ident -> Err (Typ, Ident, [FArg], Blk, Integer)
-- getFun BottomState _ = Bad "function doesn't exist"
getFun state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, t_flvl, t_ilvl)) id =
  getFunR state id t_flvl t_ilvl

-- add one empty state layer on existing state
wind_state :: State -> State
wind_state BottomState =
  St (Vst [], Rst [], Ast [], Fst [], Bst [], BottomState, NotRet, 1, 1, 1)
wind_state st@(St (_, _, _, _, _, _, _, clvl, flvl, ilvl)) =
  St (Vst [], Rst [], Ast [], Fst [], Bst [], st, NotRet, clvl + 1, flvl, ilvl)

unwind_state :: State -> State
unwind_state state@(St (_, _, _, _, _, deep_s, retVal, _, _, _)) =
  case deep_s of
    -- to save the deppest state (output)
    BottomState -> state
    otherwise -> setRetValue deep_s retVal

toBuffer :: State -> Constraint -> Err State
toBuffer state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, BottomState, _, clvl, flvl, ilvl)) mesg =
    Ok (
      St( Vst vst, Rst rst, Ast ast, Fst fst, Bst (mesg:bst),
        BottomState, NotRet, clvl, flvl, ilvl))
toBuffer (St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) mesg = do
  new_state <- toBuffer stc mesg
  Ok (
    St( Vst vst, Rst rst, Ast ast, Fst fst, Bst bst,
      new_state, NotRet, clvl, flvl, ilvl))

--modify :: Ident -> Constraint -> State -> Err State
--modify id con (St st) =
--  let { mapF (i, c)
--    | i == id = (i, con)
--    | otherwise = (i , c) }
--  in
--  if (any (\(i, _) -> id == i) st)
--    then Ok (St(map mapF st))
--    else Bad "variable don't exists"

defaultValue :: Typ -> Constraint
defaultValue t = case t of
  TInt -> Eint 0
  TBool -> Ebool Constraint_False
  TString -> Estring ""
