-- Jakub Kuszneruk jk320790

module TypeChecker where

import Absshl
import ErrM
import Misc

--general funcitons
--typeCheck :: Prog -> Err State
--typeCheck (Program b) = checkBlock b (St [])
--
--checkBlock :: Blk -> State -> Err State
--checkBlock b st = Ok $St []
