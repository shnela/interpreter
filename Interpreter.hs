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
    state <- loadDeclarations dec $ wind_state st;
    state <- runStatments stm state;
    Ok $ unwind_state state
  }


--declarations
loadDeclarations :: [Dec] -> State -> Err State
loadDeclarations [] st = Ok st
loadDeclarations (d:decs) st@(St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl))  = case d of
  Declaration t id -> do {
--    tmp <- toBuffer st $ Eint (100 + clvl);
--    new_state <- (declare tmp t id $ defaultValue t);
    new_state <- (declare st t id $ defaultValue t);
    loadDeclarations decs new_state
    }
  DeclarationAssing t id e -> do {
    (st, exp) <- evalExpression e st;
--    tmp <- toBuffer st $ Eint (100 + clvl);
--    new_state <- (declare tmp t id exp);
    new_state <- (declare st t id exp);
    loadDeclarations decs new_state
    }
  DeclarationFunc t id args blk -> do {
    new_state <- (declareF st t id args blk);
    loadDeclarations decs new_state
  }

-- for helper
runFor id end_val blk state = do
  Eint counter <- lookvar state id
  if counter < end_val then do
      new_state <- interpretBlock blk state;
      incremented_state <- update new_state id $Eint (counter + 1);
      runFor id end_val blk incremented_state
  else return state

--statements
runStatments :: [Stm] -> State -> Err State
runStatments [] state = Ok state
runStatments (s:t) state = do
  new_state@(St (_, _, _, _, _, ret, _, _, _)) <- case s of
    ForLoop id exp blk -> do {
        (state, end_cons) <- evalExpression exp state;
        case end_cons of
        Eint end_val -> do
          initial_state <- declare (wind_state state) TInt id (Eint 0);
          finish_state <- runFor id end_val blk initial_state;
          Ok $ unwind_state finish_state
        otherwise ->  Bad "For loop range must be integer"
    }

    IfStmt exp blk -> do {
      (state, c) <- evalExpression exp state;
      condition <- convert_constraint_to_bool c;
      new_state <-
        if condition then interpretBlock blk state
          else Ok state;
      Ok new_state
    }

    IfElseStmt exp blkt blke -> do {
      (state, c) <- evalExpression exp state;
      condition <- convert_constraint_to_bool c;
      new_state <-
        if condition then interpretBlock blkt state
          else interpretBlock blke state;
      Ok new_state
    }

    PrintStmt exp -> do {
      (state, e) <- evalExpression exp state;
      new_state <- toBuffer state e;
      Ok new_state
    }

    ReturnStmt exp -> do {
      (state@(St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)), cons) <- evalExpression exp state;
      Ok $ St(
        Vst vst,
        Rst rst,
        Fst fst,
        Bst bst,
        stc,
        Return cons,
        clvl,
        flvl,
        ilvl)
    }

    ExpStmt exp -> do {
      (state, _) <- evalExpression exp state;
      Ok state
    }
    
    Assign v e -> do {
      (state, val) <- evalExpression e state;
      new_state <- update state v val;
      Ok new_state
    }

  case ret of
    Return _ -> Ok new_state
    NotRet -> runStatments t new_state

-- update state with funciton arguments
enrich:: State -> Ident -> [(FArg, IParam)] -> Err State
enrich state id [] = Ok state
enrich state id ((arg, InvokeParamater param):rest) = do
   new_state <- case arg of
     FArgument t i ->  do
      (state, cons) <- evalExpression param state;
      declare state t i cons
--     FArgumentFun t i args -> do
--      declareF state t i args
     FArgumentRef t i -> 
       case param of
         Evar param_id -> refer state t i t param_id
         otherwise -> Bad "only var or value in funciton invoke";
   enrich new_state id rest

--expresions
evalExpression :: Exp -> State -> Err (State, Constraint)
evalExpression e state@(St (Vst vst, Rst rst, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) =
  let eval e1 e2 f = do {
    (state, x) <- evalExpression e1 state;
    (state, y) <- evalExpression e2 state;
    case (x, y) of
    (Eint xi, Eint yi) -> Ok (state, Eint $ f xi yi)
    _ -> Bad "Bad operation"
  } in let evalB e1 e2 f = do {
    (state, x) <- evalExpression e1 state;
    (state, y) <- evalExpression e2 state;
    case (x, y) of
    (Eint xi, Eint yi) -> Ok (state, Ebool $ if f xi yi then Constraint_True else Constraint_False)
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
  Einvok id params -> do {
    (typ, id, fargs, blk, f_st) <- getFun state id;
    enriched_start_state <- enrich (wind_state state) id (zip fargs $ params);
    new_start_state <- Ok $ setFlvl enriched_start_state f_st clvl;
--    tmp <- toBuffer new_start_state $ Eint clvl;
--    tmp2 <- toBuffer tmp $ Eint f_st;
--    tmp3 <- toBuffer tmp2 $ Eint clvl;
--    new_state <- interpretBlock blk tmp3;
    new_state <- interpretBlock blk new_start_state;
    ret_val <- getRetValue new_state;
    ret_type <- getType ret_val;
    if typ /= ret_type then Bad $"Bad return type: " ++ (show ret_type) ++ ", " ++ (show typ) ++ " expected."
      else Ok (unwind_state new_state, ret_val)
  }
  Evar id -> do {
--    tmp <- toBuffer state $ Eint (200 + clvl);
--    tmp2 <- toBuffer tmp $ Eint (200 + flvl);
--    tmp3 <- toBuffer tmp2 $ Eint (200 + ilvl);
--    val <- lookvar state id;
--    Ok (tmp3, val)
    val <- lookvar state id;
    Ok (state, val)
  }
  Econst cons -> do {
    Ok (state, cons)
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
