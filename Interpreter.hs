-- Jakub Kuszneruk jk320790

module Interpreter where

import Control.Monad.Trans
import Control.Monad.IO.Class
import Control.Monad (MonadPlus(..), liftM)

import Absshl
import ErrM
import Misc


--general funcitons
interpret :: Prog -> Err State
interpret (Program b) = interpretBlock b BottomState

interpretBlock :: Blk -> State -> Err State
interpretBlock b st = case b of
  Block dec stm -> do {
    state <- loadDeclarations dec (St (Vst [], Fst [], Bst [], st));
    new_state <- runStatments stm state;
    Ok new_state 
  }


--declarations
loadDeclarations :: [Dec] -> State -> Err State
loadDeclarations [] st = Ok st
loadDeclarations (d:decs) st  = case d of
  Declaration t id -> do {
    new_state <- (declare st t id $defaultValue t);
    loadDeclarations decs new_state
    }
  DeclarationAssing t id e -> do {
    exp <- evalExpression e st;
    new_state <- (declare st t id exp);
    loadDeclarations decs new_state
    }
  DeclarationFunc t id args blk -> do {
    new_state <- (declareF st t id args blk);
    loadDeclarations decs new_state
  }

runFor counter end_val blk state =
  if counter < end_val then do
      new_state <- interpretBlock blk state;
      runFor (counter + 1) end_val blk new_state
  else return state

--statements
runStatments :: [Stm] -> State -> Err State
runStatments [] state = Ok state
runStatments (s:t) state = do
  new_state <- case s of
--    ForLoop id exp blk  -> Bad "Not implemented! for"
    ForLoop id exp blk -> do {
        Eint end_val <- evalExpression exp state;
        initial_state <- declare (St (Vst [], Fst [], Bst [], state)) TInt id (Eint 0);
        finish_state <- runFor 0 end_val blk initial_state;
        Ok finish_state
    }

    IfStmt exp blk -> do {
      c <- evalExpression exp state;
      condition <- convert_constraint_to_bool c;
      new_state <-
        if condition then interpretBlock blk state
          else Ok state;
      Ok new_state
    }

    IfElseStmt exp blkt blke -> do {
      c <- evalExpression exp state;
      condition <- convert_constraint_to_bool c;
      new_state <-
        if condition then interpretBlock blkt state
          else interpretBlock blke state;
      Ok new_state
    }

    PrintStmt exp -> do {
      e <- evalExpression exp state;
      new_state <- toBuffer state e;
      Ok new_state
    }

    ReturnStmt exp -> Bad "Not implemented! return"
    ExpStmt exp -> do {
      evalExpression exp state;
      Ok state
    }
    
    Assign v e -> do {
      val <- evalExpression e state;
      new_state <- update state v val;
      Ok new_state
    }
  runStatments t new_state


--expresions
evalExpression :: Exp -> State -> Err Constraint
evalExpression e state =
  let eval e1 e2 f = do {
    x <- evalExpression e1 state;
    y <- evalExpression e2 state;
    case (x, y) of
    (Eint xi, Eint yi) -> Ok $ Eint $ f xi yi
    _ -> Bad "Bad operation"
  } in let evalB e1 e2 f = do {
    x <- evalExpression e1 state;
    y <- evalExpression e2 state;
    case (x, y) of
    (Eint xi, Eint yi) -> Ok $ Ebool $ if f xi yi then Constraint_True else Constraint_False
    _ -> Bad "Bad operation"
  } in case e of
  Eeq e1 e2 -> evalB e1 e2 (==)
  Eneq e1 e2 -> evalB e1 e2 (/=)
  Elthen e1 e2 -> evalB e1 e2 (<)
  Egrthen e1 e2 -> evalB e1 e2 (>)
  Ele e1 e2 -> evalB e1 e2 (<=)
  Ege e1 e2 -> evalB e1 e2 (>=)
  Eplus e1 e2 -> eval e1 e2 (+)
  Eminus e1 e2 -> eval e1 e2 (-)
  Etimes e1 e2 -> eval e1 e2 (*)
  Ediv e1 e2 -> eval e1 e2 quot
--   Einvok id params -> do {
--     (typ, id, fargs, blk) <- getFun id state;
--     new_start_state <- enrich state id zip $ fargs params;
--     new_state <- interpretBlock blk new_start_state;
--     case typ of
--       TInt -> Ok $ Eint 0
--       otherwise -> Ok $ Ebool Constraint_False
--   }
  Evar id -> do {
    val <- lookvar state id;
    Ok val
  }
  Econst cons -> do {
    Ok cons
--    case cons of
--      Eint i -> Ok (Eint i)
--      Ebool b -> if b then Ok $ Ebool Constraint_True else Ok $ Ebool Constraint_False
--      Estring str -> Ok $Estring str
--      otherwise -> Bad "lol patternmaching"
  }

evalConstraint2int :: Constraint -> Err Integer
evalConstraint2int c = case c of
 Eint i -> Ok i
-- Ebool Constraint_True -> Bad "Can't turn bool to int"
-- Constraint_False -> Bad "Can't turn bool to int"
 Estring s -> Bad "can't turn string to int"

convert_constraint_to_bool :: Constraint -> Err Bool
convert_constraint_to_bool c = case c of
      Ebool b -> return $ b == Constraint_True
      Eint i -> return $ i /= 0
      Estring _ -> Bad "cannot convert string to Boolean"
      otherwise -> Bad "cannot convert to Boolean"
