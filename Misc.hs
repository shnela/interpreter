-- Jakub Kuszneruk jk320790

module Misc where

import Absshl
import ErrM

--type Ident = String
--  deriving Eq

data VarState = Vst[(Typ, Ident, Constraint)]
  deriving Show
data FunState = Fst[(Typ, Ident, [FArg], Blk)]
  deriving Show
data BufState = Bst[Constraint]
  deriving Show
--data StackState = St[State]
--  deriving Show

data State = St(VarState, FunState, BufState, State) | BottomState
  deriving Show

lookvar :: State -> Ident -> Err Constraint
lookvar BottomState id = Bad $ "no such varbiable: " ++ (show id)
lookvar (St (Vst vst, Fst fst, Bst bst, stc)) id =
  let {find found (t, i, c)
    | i == id = (t, i, c)
    | otherwise = found }
  in
  if (any (\(_, i, _) -> id == i) vst)
    then Ok ((\(_, _, c) -> c)(foldl find (head vst) vst))
    else lookvar stc id

--TODO type check
update :: State -> Ident -> Constraint -> Err State
update BottomState _ _ = Bad "no such identifier to update"
update (St (Vst vst, Fst fst, Bst bst, stc)) id con =
  let { updateV el@(t, i, c)
        | i == id = (t, i, con)
        | otherwise = el }
    in
    if (any (\(_, i, _) -> id == i) vst)
      then
        Ok $ St(
          Vst (map updateV vst),
          Fst fst,
          Bst bst,
          stc)
      else do
        updated_state <- update stc id con;
        Ok $ St(
          Vst vst,
          Fst fst,
          Bst bst,
          updated_state)

declare :: State -> Typ -> Ident -> Constraint -> Err State
declare state@(St (Vst vst, Fst fst, Bst bst, stc)) typ id con =
  if (any (\(_, i, _) -> id == i) vst)
    then Bad "Identifier is declared in this scope"
    else Ok (St(
      Vst ((typ, id, con):vst),
      Fst fst,
      Bst bst,
      stc))

declareF :: State -> Typ -> Ident -> [FArg] -> Blk -> Err State
declareF (St (Vst vst, Fst fst, Bst bst, BottomState)) typ id args blk =
  if (any (\(_, i, _, _) -> id == i) fst)
    then Bad "function exists"
    else Ok (St(
      Vst vst,
      Fst ((typ, id, args, blk):fst),
      Bst bst,
      BottomState))
declareF _ _ _ _ _ = Bad "function declaration allowed only in outermost block"
-- TODO example

getFun :: Ident -> State -> Err (Typ, Ident, [FArg], Blk)
getFun id BottomState = Bad "function doesn't exists"
getFun id (St (Vst vst, Fst fst, Bst bst, BottomState)) =
  let {find found (t, i, a, c)
    | i == id = (t, i, a, c)
    | otherwise = found }
  in if (any (\(_, i, _, _) -> id == i) fst)
    then Ok (foldl find (head fst) fst)
    else Bad "function doesn't exists"
getFun id (St (Vst vst, Fst fst, Bst bst, stc)) =
  getFun id stc

-- enrich:: State -> Ident -> [(FArg, IParam)] -> Err State
-- enrich state id [] = Ok state
-- enrich state id (arg, param:rest) = do {
--   new_state <-
--     if arg == FArgument t i then
--       if param == Econst cons then declare state t i cons
--         else if param == Evar id then
--           cons <- lookvar state id;
--           declare state t i cons
--           else Bad "only var or vale in funciton invoke"
--       else if arg == ArgumentRef t i then 
--         if param == Econst cons then declare state t i cons
--           else if param == Evar id then
--             cons <- lookvar state id;
--             declare state t i cons
--             else Bad "only var or vale in funciton invoke";
--       Ok New State
-- }
--    case arg of
--      FArgument t i -> 
--        case param of
--          Econst cons -> declare state t i cons
--          Evar id ->
--            cons <- lookvar state id;
--            declare state t i cons
--          otherwise -> Bad "only var or value in funcito invoke"
--      FArgumentRef t i -> 
--        case param of
--          Econst cons -> declare state t i cons
--          Evar id ->
--            cons <- lookvar state id;
--            declare state t i cons
--          otherwise -> Bad "only var or value in funcito invoke";
--      Ok new_state

toBuffer :: State -> Constraint -> Err State
toBuffer (St (Vst vst, Fst fst, Bst bst, BottomState)) mesg =
    Ok (St(
      Vst vst,
      Fst fst,
      Bst (mesg:bst),
      BottomState))
toBuffer (St (Vst vst, Fst fst, Bst bst, stc)) mesg =
  toBuffer stc mesg

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
