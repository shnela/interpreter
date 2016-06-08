

module Absshl where

-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq,Ord,Show,Read)
data Prog =
   Program Blk
  deriving (Eq,Ord,Show,Read)

data Blk =
   Block [Dec] [Stm]
  deriving (Eq,Ord,Show,Read)

data Stm =
   ForLoop Ident Exp Blk
 | IfStmt Exp Blk
 | IfElseStmt Exp Blk Blk
 | ReturnStmt Exp
 | PrintStmt Exp
 | ExpStmt Exp
 | AssignMultiple [AssM] [Exp]
  deriving (Eq,Ord,Show,Read)

data AssM =
   AssignVar Ident
 | AssignArr Ident Exp
  deriving (Eq,Ord,Show,Read)

data AssE =
   AssignExp Exp
  deriving (Eq,Ord,Show,Read)

data Dec =
   Declaration Typ Ident
 | DeclarationAssing Typ Ident Exp
 | DeclarationFunc Typ Ident [FArg] Blk
 | DeclarationArray Typ Ident Exp
  deriving (Eq,Ord,Show,Read)

data FArg =
   FArgument Typ Ident
 | FArgumentAssing Typ Ident Exp
 | FArgumentFunc Typ Ident [FArg]
 | FArgumentRef Typ Ident
 | FArgumentArr Typ Ident
  deriving (Eq,Ord,Show,Read)

data Typ =
   TInt
 | TBool
 | TString
  deriving (Eq,Ord,Show,Read)

data Exp =
   Eeq Exp Exp
 | Eneq Exp Exp
 | Elthen Exp Exp
 | Egrthen Exp Exp
 | Ele Exp Exp
 | Ege Exp Exp
 | Eplus Exp Exp
 | Eminus Exp Exp
 | Etimes Exp Exp
 | Ediv Exp Exp
 | Einc Ident
 | Edec Ident
 | Einvok Ident [IParam]
 | Evar Ident
 | Econst Constraint
 | Elmb [FArg] Exp
 | Earr Ident Exp
  deriving (Eq,Ord,Show,Read)

data Constraint =
   Eint Integer
 | Ebool BoolT
 | Estring String
  deriving (Eq,Ord,Show,Read)

data BoolT =
   Constraint_True
 | Constraint_False
  deriving (Eq,Ord,Show,Read)

data IParam =
   InvokeParamater Exp
  deriving (Eq,Ord,Show,Read)

