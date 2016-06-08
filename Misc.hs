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
data ArrState = Ast[(Typ, Ident, [Constraint], Integer)]
  deriving Show
data FunState = Fst[(Typ, Ident, [FArg], Blk, Integer)]
  deriving Show
data BufState = Bst[String]
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

updateV id con el@(t, i, c)
  | i == id = (t, i, con)
  | otherwise = el
getVarType id oldt (t, i, _)
  | i == id = t
  | otherwise = oldt
-- to invoke this functio you have to be sure that id is declared in this vst
updateVarState id vst con =
  let
    dec_t = foldl (getVarType id) TInt vst
    in do {
      converted_con <- convert_to_proper_val con dec_t;
      Ok $ map (updateV id converted_con) vst
    }

updateR :: State -> Ident -> Constraint -> Integer -> Integer -> Err State
updateR BottomState id con top_flvl top_ilvl =
  case getType con of
  Ok t -> Bad $ "No such identifier: " ++ (show id) ++ " of type: " ++ (show t) ++ " to update."
  otherwise -> Bad "Unknown error during resolving variable type"
updateR (St (Vst vst, Rst rst, Ast ast,Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) id con top_flvl top_ilvl =
    if ((clvl <= top_flvl || clvl > top_ilvl) && any (\(t, i, _) -> id == i) vst)
      then do {
        updated_vst <- updateVarState id vst con;
        Ok $ St((Vst updated_vst), Rst rst, Ast ast, Fst fst, Bst bst, stc,
          NotRet, clvl, flvl, ilvl)
      }
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
  if (any (\(_, i, _) -> id == i) vst) || (any (\(_, i, _, _) -> id == i) ast)
    then Bad "Identifier is declared in this scope"
      else do {
        converted_con <- convert_to_proper_val con typ;
        Ok (
          St(Vst ((typ, id, converted_con):vst), Rst rst, Ast ast, Fst fst, Bst bst, stc,
            NotRet, clvl, flvl, ilvl))
        }

-- declare for references
referH :: State -> Typ -> Ident -> Ident -> Err State
referH state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) typ id1 id2 =
  if (any (\(_, i, _) -> id1 == i) rst) then Bad "Reference is declared in this scope"
    else if any (\(t, i, _) -> id2 == i && (typ == t)) vst
      then Bad "No such variable to map"
      else Ok (
        St(Vst vst, Rst ((typ, id1, id2):rst), Ast ast, Fst fst, Bst bst, stc,
          NotRet, clvl, flvl, ilvl))

refer :: State -> Typ -> Ident -> Typ -> Ident -> Err State
refer state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) typ1 id1 typ2 id2 =
  if typ1 /= typ2 then Bad "Type mismatch"
    else
      case getRefTranslation state id2 ilvl of
        Left (translated_id, _) -> referH state typ1 id1 translated_id
        Right translated_id -> referH state typ1 id1 translated_id

--         Left (translated_id, var_lvl) -> updateArrR state translated_id ix con var_lvl (clvl+99)
--         Right translated_id -> updateArrR state translated_id ix con t_flvl t_ilvl

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

-- helper function
findArrId id found (t, i, c, s)
  | i == id = (t, i, c, s)
  | otherwise = found


-- helper check size of array and idx
checkIdxOutOfBound id ix (Ast ast) =
  let arr_size = ((\(_, _, _, s) -> s)(foldl (findArrId id) (head ast) ast))
    in if ix >= arr_size
      then Bad $ "Array of size " ++ (show arr_size) ++ " cannot return idx: " ++ (show ix)
      else Ok arr_size

lookArrR :: State -> Ident -> Integer -> Integer -> Integer -> Err Constraint
lookArrR BottomState id ix _ _ = Bad $ "no such array: " ++ (show id) ++ " " ++ (show ix)
lookArrR (St (_, _, Ast ast, _, _, stc, _, clvl, _, _)) id ix top_flvl top_ilvl =
    if (clvl <= top_flvl || clvl > top_ilvl) && (any (\(_, i, _, _) -> id == i) ast)
      then do
        arr_size <- checkIdxOutOfBound id ix (Ast ast);
        if ix >= arr_size then Bad $ "Array of size " ++ (show arr_size) ++ " cannot return idx: " ++ (show ix)
          else
            Ok ((\(_, _, c, _) -> c !! (fromIntegral ix))(foldl (findArrId id) (head ast) ast))
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

updateA id ix con el@(t, i, c, s)
  | i == id = (t, i, updateIx c [] ix con 0, s)
  | otherwise = el
getArrType id oldt (t, i, _, _)
  | i == id = t
  | otherwise = oldt
-- to invoke this functio you have to be sure that id is declared in this vst
updateArrState id ix vst con =
  let
    dec_t = foldl (getArrType id) TInt vst
    in do {
      converted_con <- convert_to_proper_val con dec_t;
      Ok $ map (updateA id ix converted_con) vst
    }

updateArrR :: State -> Ident -> Integer -> Constraint -> Integer -> Integer -> Err State
updateArrR BottomState id ix con top_flvl top_ilvl =
  case getType con of
  Ok t -> Bad $ "No such identifier: " ++ (show id) ++ " of type: " ++ (show t) ++ " to update!"
  otherwise -> Bad "Unknown error during resolving variable type"
updateArrR (St (Vst vst, Rst rst, Ast ast,Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) id ix con top_flvl top_ilvl =
  let { updateA el@(t, i, c, s)
        | i == id = (t, i, updateIx c [] ix con 0, s)
        | otherwise = el }
    in
    if ((clvl <= top_flvl || clvl > top_ilvl) && any (\(t, i, _, _) -> id == i) ast)
      then do {
        updated_ast <- updateArrState id ix ast con;
        Ok $ St(Vst vst, Rst rst, Ast updated_ast, Fst fst, Bst bst, stc,
          NotRet, clvl, flvl, ilvl)
      }
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
      if (any (\(_, i, _) -> id == i) vst) || (any (\(_, i, _, _) -> id == i) ast)
        then Bad "Such id is already defined in this scope"
        else Ok (
          St(Vst vst, Rst rst, Ast ((typ, id, def_arr, siz):ast), Fst fst, Bst bst, st,
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

toBuffer :: State -> String -> Err State
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


-- default conversions
convert_constraint_to_int :: Constraint -> Err Constraint
convert_constraint_to_int c = case c of
 Eint i -> Ok $ Eint i
 Ebool Constraint_True -> Ok $ Eint 1
 Ebool Constraint_False -> Ok $ Eint 0
 Estring s -> Bad "can't turn string to int"

convert_constraint_to_bool :: Constraint -> Err Constraint
convert_constraint_to_bool c = case c of
  Ebool b -> Ok $ Ebool b
  Eint i -> if i == 0 then Ok $ Ebool Constraint_False else Ok $ Ebool Constraint_True
  Estring _ -> Bad "cannot convert string to Boolean"

convert_constraint_to_string :: Constraint -> Err Constraint
convert_constraint_to_string str = case str of
  Ebool b -> Bad "cannot convert bool to string"
  Eint i -> Bad "cannot convert int to string"
  Estring str -> Ok $ Estring str

convert_to_proper_val :: Constraint -> Typ -> Err Constraint
convert_to_proper_val con typ =
  case typ of
    TInt -> convert_constraint_to_int con
    TBool -> convert_constraint_to_bool con
    TString -> convert_constraint_to_string con
