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
data FunState = Fst[(Typ, Ident, [FArg], Blk)]
  deriving Show
data BufState = Bst[Constraint]
  deriving Show
data RetValue = Return Constraint | NotRet
  deriving Show

data State = St(VarState, RefState, FunState, BufState, State, RetValue) | BottomState
  deriving Show



getRetValue :: State -> Err Constraint
getRetValue (St (_, _, _, _, _, NotRet)) = Ok $ Eint 0
getRetValue (St (_, _, _, _, _, Return ret)) = Ok ret

setRetValue :: State -> RetValue -> State
setRetValue (St (vst, rst, fst, bst, st, _)) ret = St(vst, rst, fst, bst, st, ret)


getRefTranslation :: State -> Ident -> Err Ident
getRefTranslation BottomState id = Ok id
getRefTranslation (St (_, Rst rst, _, _, stc, _)) id =
  let {
    find found (t, i, c)
      | i == id = (t, i, c)
      | otherwise = found }
  in
  if (any (\(_, i, _) -> id == i) rst)
    then Ok ((\(_, _, c) -> c)(foldl find (head rst) rst))
    else getRefTranslation stc id

lookvarR :: State -> Ident -> Err Constraint
lookvarR BottomState id = Bad $ "no such varbiable: " ++ (show id)
lookvarR state@(St (Vst vst, Rst rst, _, _, stc, _)) id =
  let {
    find found (t, i, c)
      | i == id = (t, i, c)
      | otherwise = found }
  in do {
  if (any (\(_, i, _) -> id == i) vst)
    then Ok ((\(_, _, c) -> c)(foldl find (head vst) vst))
    else lookvarR stc id
  }

lookvar :: State -> Ident -> Err Constraint
lookvar state@(St (Vst vst, Rst rst, _, _, stc, _)) id = do
  translated_id <- getRefTranslation state id;
  lookvarR state translated_id

getType :: Constraint -> Err Typ
getType con =
  case con of
  Eint _ -> Ok TInt
  Ebool _ -> Ok TBool
  Estring _ -> Ok TString
  otherwise -> Bad "Unknown type"

updateR :: State -> Ident -> Constraint -> Err State
updateR BottomState id con =
  case getType con of
  Ok t -> Bad $ "No such identifier: " ++ (show id) ++ " of type: " ++ (show t) ++ " to update."
  otherwise -> Bad "Unknown error during resolving variable type"
updateR (St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _)) id con =
  let { updateV el@(t, i, c)
        | i == id = (t, i, con)
        | otherwise = el }
    in
    if (any (\(t, i, _) -> id == i && (getType con == Ok t)) vst)
      then
        Ok $ St(
          Vst (map updateV vst),
          Rst rst,
          Fst fst,
          Bst bst,
          stc,
          NotRet)
      else do
        updated_state <- updateR stc id con;
        Ok $ St(
          Vst vst,
          Rst rst,
          Fst fst,
          Bst bst,
          updated_state,
          NotRet)
update :: State -> Ident -> Constraint -> Err State
update state@(St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _)) id con = do
  id <- getRefTranslation state id;
  v <- lookvarR state id;
  updateR state id con

declare :: State -> Typ -> Ident -> Constraint -> Err State
declare state@(St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _)) typ id con =
  if (any (\(_, i, _) -> id == i) vst)
    then Bad "Identifier is declared in this scope"
    else Ok (St(
      Vst ((typ, id, con):vst),
      Rst rst,
      Fst fst,
      Bst bst,
      stc,
      NotRet))

-- declare for references
refer :: State -> Typ -> Ident -> Typ -> Ident -> Err State
refer state@(St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _)) typ1 id1 typ2 id2 =
  if typ1 /= typ2 then Bad "Type mismatch"
    else
    if (any (\(_, i, _) -> id1 == i) rst) then Bad "Reference is declared in this scope"
      else if any (\(t, i, _) -> id2 == i && (typ1 == t)) vst
        then Bad "No such variable to map"
        else Ok (St(
          Vst vst,
          Rst ((typ1, id1, id2):rst),
          Fst fst,
          Bst bst,
          stc,
          NotRet))

declareF :: State -> Typ -> Ident -> [FArg] -> Blk -> Err State
declareF (St (Vst vst, Rst rst, Fst fst, Bst bst, BottomState, _)) typ id args blk =
  if (any (\(_, i, _, _) -> id == i) fst)
    then Bad "function exists"
    else Ok (St(
      Vst vst,
      Rst rst,
      Fst ((typ, id, args, blk):fst),
      Bst bst,
      BottomState,
      NotRet))
declareF _ _ _ _ _ = Bad "function declaration allowed only in outermost block"

getFun :: Ident -> State -> Err (Typ, Ident, [FArg], Blk)
getFun id BottomState = Bad "function doesn't exists"
getFun id (St (Vst vst, Rst rst, Fst fst, Bst bst, BottomState, _)) =
  let {find found (t, i, a, c)
    | i == id = (t, i, a, c)
    | otherwise = found }
  in if (any (\(_, i, _, _) -> id == i) fst)
    then Ok (foldl find (head fst) fst)
    else Bad "function doesn't exists"
getFun id (St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _)) =
  getFun id stc

-- add one empty state layer on existing state
wind_state :: State -> State
wind_state st = St (Vst [], Rst [], Fst [], Bst [], st, NotRet)

unwind_state :: State -> State
unwind_state state@(St (_, _, _, _, deep_s, retVal)) =
  case deep_s of
    -- to save the deppest state (output)
    BottomState -> state
    otherwise -> setRetValue deep_s retVal

toBuffer :: State -> Constraint -> Err State
toBuffer state@(St (Vst vst, Rst rst, Fst fst, Bst bst, BottomState, _)) mesg = do
    Ok (St(
      Vst vst,
      Rst rst,
      Fst fst,
      Bst (mesg:bst),
      BottomState,
      NotRet))
toBuffer (St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _)) mesg = do
  new_state <- toBuffer stc mesg
  Ok (St(
    Vst vst,
    Rst rst,
    Fst fst,
    Bst bst,
    new_state,
    NotRet))

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
