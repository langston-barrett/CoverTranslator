%
% (c) The University of Glasgow 2001
%
\begin{code}

module ExternalCore where


data Module 
 = Module Mname [Tdef] [Vdefg]

data Tdef 
  = Data (Qual Tcon) [Tbind] [Cdef]
  | Newtype (Qual Tcon) [Tbind] (Maybe Ty)

data Cdef 
  = Constr (Qual Dcon) [Tbind] [Ty]

data Vdefg 
  = Rec [Vdef]
  | Nonrec Vdef

type Vdef = (Qual Var,Ty,Exp) 

data Exp 
  = Var (Qual Var)
  | Dcon (Qual Dcon)
  | Lit Lit
  | App Exp Exp
  | Appt Exp Ty
  | Lam Bind Exp          
  | Let Vdefg Exp
  | Case Exp Vbind [Alt] {- non-empty list -}
  | Coerce Ty Exp 
  | Note String Exp
  | External String Ty

data Bind 
  = Vb Vbind
  | Tb Tbind

data Alt 
  = Acon (Qual Dcon) [Tbind] [Vbind] Exp
  | Alit Lit Exp
  | Adefault Exp

type Vbind = (Var,Ty)
type Tbind = (Tvar,Kind)

data Ty 
  = Tvar Tvar
  | Tcon (Qual Tcon)
  | Tapp Ty Ty
  | Tforall Tbind Ty 

data Kind 
  = Klifted
  | Kunlifted
  | Kopen
  | Karrow Kind Kind

data Lit 
  = Lint Integer Ty
  | Lrational Rational Ty
  | Lchar Char Ty
  | Lstring String Ty
  

type Mname = Id
type Var = Id
type Tvar = Id
type Tcon = Id
type Dcon = Id

type Qual t = (Mname,t)

type Id = String

primMname = "GHCziPrim"

tcArrow :: Qual Tcon
tcArrow = (primMname, "ZLzmzgZR")

\end{code}




