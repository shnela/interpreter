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
loadDeclarations (d:decs) st@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl))  = case d of
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
  DeclarationArray t id siz_exp -> do {
    siz <- evalExpressionArrayIdx siz_exp st;
    new_state <- (declareA st t id siz $ defaultValue t);
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
  new_state@(St (_, _, _, _, _, _, ret, _, _, _)) <- case s of
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
      condition <- convert_constraint_to_haskell_bool c;
      new_state <-
        if condition then interpretBlock blk state
          else Ok state;
      Ok new_state
    }

    IfElseStmt exp blkt blke -> do {
      (state, c) <- evalExpression exp state;
      condition <- convert_constraint_to_haskell_bool c;
      new_state <-
        if condition then interpretBlock blkt state
          else interpretBlock blke state;
      Ok new_state
    }

    PrintStmt exp -> 
      case exp of
        otherwise -> do {
          (state, e) <- evalExpression exp state;
          new_state <- toBuffer state (show e);
          Ok new_state
        }

    ReturnStmt exp -> do {
      (state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)), cons) <- evalExpression exp state;
      Ok $ St(
        Vst vst,
        Rst rst,
        Ast ast,
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
    
--     Assign v e -> do {
--       (state, val) <- evalExpression e state;
--       new_state <- update state v val;
--       Ok new_state
--     }
--     
--     AssignArr v ix_exp e -> do {
--       ix <- evalExpressionArrayIdx ix_exp state;
--       (state, val) <- evalExpression e state;
--       new_state <- updateArr state v ix val;
--       Ok new_state
--     }
    
    AssignMultiple vars exps ->
      if length vars /= length exps
        then Bad "Number of variables to assign and values to assign should be equal."
        else do {
          new_state <- assignValues vars exps state;
          Ok new_state
        }

  case ret of
    Return _ -> Ok new_state
    NotRet -> runStatments t new_state

-- helper function
the_same_type a1 a2 =
  case (a1, a2) of
    (FArgument t1 _, FArgument t2 _) -> True
    (FArgumentAssing t1 _ _, FArgumentAssing t2 _ _) -> True
    (FArgumentFunc t1 _ _, FArgumentFunc t2 _ _) -> True
    (FArgumentRef t1 _, FArgumentRef t2 _) -> True
    otherwise -> False

-- helper function
correct_lmb_args d_args a_args =
  length d_args == length a_args
    && (all (\(a1, a2) -> the_same_type a1 a2) $ zip d_args a_args)

-- update state with funciton arguments
enrich:: State -> Ident -> [(FArg, IParam)] -> Err State
enrich state id [] = Ok state
enrich state id ((arg, param):rest) = do
   new_state <- case (arg, param) of
     (FArgument t i, InvokeParamater par) ->  do
      (state, cons) <- evalExpression par state;
      declare state t i cons
     (FArgumentRef t i, InvokeParamater par) -> 
       case par of
         Evar param_id -> refer state t i t param_id
         otherwise -> Bad "only var or value in funciton invoke";
     (FArgumentFunc t i args, InvokeParamater (Evar (Ident f_arg_name))) -> do
        (typ, id, fargs, blk, f_st) <- getFun state (Ident f_arg_name);
        declareF state t i args blk
     (FArgumentFunc t i args, InvokeParamater (Elmb fargs exp)) ->
        if correct_lmb_args args fargs then
          declareF state t i fargs (Block [] [ReturnStmt exp])
          else
            Bad $ "Bad lambda argument."
     (FArgumentFunc t _ _, _) -> Bad $ "Function returning " ++ (show t) ++ " expected."
     (FArgumentArr t i, InvokeParamater (Evar id)) ->
--         do  {
--           tmp <- toBuffer state $ (show i);
--           tmp2 <- toBuffer tmp $ (show id);
--           refer tmp2 t i t id
--         }
        refer state t i t id
     (FArgumentArr t i, _) -> Bad $ "Array of type " ++ (show t) ++ " expected."
   enrich new_state id rest

evalExpressionArrayIdx :: Exp -> State -> Err Integer
evalExpressionArrayIdx idx_exp state = do
  (_, idx_constraint) <- evalExpression idx_exp state;
  case idx_constraint of
    Eint idx -> Ok idx
    otherwise -> Bad "Array indexes should be integers"

-- helper for multi assign
assignValues :: [AssM] -> [Exp] ->  State -> Err State
assignValues [] [] state = Ok state
assignValues (v:vars) (e:exps) state = do
  new_state <- assignOne v e state;
  assignValues vars exps new_state

assignOne :: AssM -> Exp -> State -> Err State
assignOne (AssignVar v) expression state = do {
  (state, val) <- evalExpression expression state;
  new_state <- update state v val;
  Ok new_state
}
assignOne (AssignArr v ix_e) exp state = do {
  ix <- evalExpressionArrayIdx ix_e state;
  (state, val) <- evalExpression exp state;
  new_state <- updateArr state v ix val;
  Ok new_state
}

--expresions
evalExpression :: Exp -> State -> Err (State, Constraint)
evalExpression e state@(St (Vst vst, Rst rst, Ast ast, Fst fst, Bst bst, stc, _, clvl, flvl, ilvl)) =
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
  Earr id ix_exp -> do {
    ix <- evalExpressionArrayIdx ix_exp state;
    val <- lookArr state id ix;
    Ok (state, val)
  }

convert_constraint_to_haskell_bool :: Constraint -> Err Bool
convert_constraint_to_haskell_bool c = case c of
  Ebool b -> return $ b == Constraint_True
  Eint i -> return $ i /= 0
  Estring _ -> Bad "cannot convert string to Boolean"
