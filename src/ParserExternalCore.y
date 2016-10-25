{
module ParserExternalCore ( parseCore, module ParserCoreUtils ) where
import ExternalCore  -- Abstract syntax for external core
import ParserCoreUtils
import LexCore
}

%name parseCore
%tokentype { Token }

%token
 '%module'	{ TKmodule }
 '%data'	{ TKdata }
 '%newtype'	{ TKnewtype }
 '%forall'	{ TKforall }
 '%rec'		{ TKrec }
 '%let'		{ TKlet }
 '%in'		{ TKin }
 '%case'	{ TKcase }
 '%of'		{ TKof }
 '%coerce'	{ TKcoerce }
 '%note'	{ TKnote }
 '%external'	{ TKexternal }
 '%_'		{ TKwild }
 '('		{ TKoparen }
 ')'		{ TKcparen }
 '{'		{ TKobrace }
 '}'		{ TKcbrace }
 '#' 		{ TKhash}
 '='		{ TKeq }
 '::'		{ TKcoloncolon }
 '*'		{ TKstar }
 '->'		{ TKrarrow }
 '\\'		{ TKlambda}
 '@'		{ TKat }
 '.'		{ TKdot }
 '?'		{ TKquestion}
 ';'            { TKsemicolon }
 NAME		{ TKname $$ }
 CNAME 		{ TKcname $$ }
 INTEGER	{ TKinteger $$ }
 RATIONAL	{ TKrational $$ }
 STRING		{ TKstring $$ }
 CHAR		{ TKchar $$ }

%monad { P } { thenP } { returnP }
%lexer { lexer } { TKEOF }

%%

module	:: { Module }
         : '%module' modid tdefs vdefgs
		{ Module $2 $3 $4 }

modid	:: { Mname }
	: CNAME	                 { $1 }

-------------------------------------------------------------
--     Type and newtype declarations

tdefs	:: { [Tdef] }
	: {- empty -}	{[]}
	| tdef ';' tdefs	{$1:$3}

tdef	:: { Tdef }
	: '%data' q_tc_name tv_bndrs '=' '{' cons1 '}'
                { Data $2 $3 $6 }
	| '%newtype' q_tc_name tv_bndrs trep 
		{ Newtype $2 $3 $4 }

trep    :: { Maybe Ty }
        : {- empty -}   { Nothing }
        | '=' ty        { Just $2 }

cons1	:: { [Cdef] }
	: con		{ [$1] }
	| con ';' cons1	{ $1:$3 }

con	:: { Cdef }
	: d_pat_occ attv_bndrs hs_atys 
		{ Constr $1 $2 $3 }

attv_bndrs :: { [Tbind] }
	: {- empty -} 	         { [] }
	| '@' tv_bndr attv_bndrs { $2 : $3 }

hs_atys :: { [Ty] }
         : atys               { $1 }


---------------------------------------
--                 Types
---------------------------------------

atys	:: { [Ty] }
	: {- empty -}   { [] }
	| aty atys      { $1:$2 }

aty	:: { Ty }
	: tv_occ     { Tvar $1 }
	| q_tc_name  { Tcon $1 }
	| '(' ty ')' { $2 }

bty	:: { Ty }
	: aty	 { $1 }
        | bty aty { Tapp $1 $2 }

ty	:: { Ty }
	: bty	                     { $1 }
	| bty '->' ty                { tArrow $1 $3 }
	| '%forall' tv_bndrs '.' ty  { foldr Tforall $4 $2 }

----------------------------------------------
--        Bindings

vdefgs	:: { [Vdefg] }
	: {- empty -}	        { [] }
	| let_bind ';' vdefgs	{ $1 : $3 }

let_bind :: { Vdefg }
	: '%rec' '{' vdefs1 '}' { Rec $3 }
	|  vdef                 { Nonrec $1  }

vdefs1	:: { [Vdef] }
	: vdef		        { [$1] }
	| vdef ';' vdefs1       { $1:$3 }

vdef	:: { Vdef }
	: q_var '::' ty '=' exp { ($1, $3, $5) }

qd_occ :: { Var }
        : var_occ { $1 }
        | d_occ   { $1 }

---------------------------------------
--  Binders
bndr	:: { Bind }
        : '@' tv_bndr 	{ Tb $2 }
	| id_bndr	{ Vb $1 }

bndrs 	:: { [Bind] }
	: bndr		{ [$1] }
	| bndr bndrs	{ $1:$2 }

id_bndr	:: { Vbind }
	: '(' var_occ '::' ty ')'	{ ($2,$4) }

id_bndrs :: { [Vbind] }
	: {-empty -}    	{ [] }
	| id_bndr id_bndrs	{ $1:$2 }

tv_bndr	:: { Tbind }
	:  tv_occ                    { ($1, Klifted) }
	|  '(' tv_occ '::' akind ')' { ($2, $4) }

tv_bndrs:: { [Tbind] }
	: {- empty -}	{ [] }
	| tv_bndr tv_bndrs	{ $1:$2 }

akind	:: { Kind }
	: '*' 		{Klifted}	
	| '#'		{Kunlifted}
	| '?'		{Kopen}
        | '(' kind ')'	{ $2 }

kind 	:: { Kind }
	: akind 	{ $1 }
	| akind '->' kind { Karrow $1 $3 }

-----------------------------------------
--             Expressions

aexp    :: { Exp }
	: var_occ                { Var  ("", $1) }
	| modid '.' var_occ      { Var  ($1, $3) }
	| d_occ	                 { Dcon ("", $1) }
	| modid '.' d_occ	 { Dcon ($1, $3) }
	| lit		{ Lit $1 }
	| '(' exp ')' 	{ $2 }

fexp	:: { Exp }
	: fexp aexp	{ App $1 $2 }
	| fexp '@' aty	{ Appt $1 $3 }
	| aexp		{ $1 }

exp	:: { Exp }
	: fexp		              { $1 }
	| '\\' bndrs '->' exp 	      { foldr Lam $4 $2 }
	| '%let' let_bind '%in' exp   { Let $2 $4 }
	| '%case' aexp '%of' id_bndr
	  '{' alts1 '}'		      { Case $2 $4 $6 }
	| '%coerce' aty exp   	      { Coerce $2 $3 }
	| '%note' STRING exp 	      { Note $2 $3 }
        | '%external' STRING aty      { External $2 $3 }

alts1	:: { [Alt] }
	: alt		{ [$1] }
	| alt ';' alts1	{ $1:$3 }

alt	:: { Alt }
	: d_pat_occ attv_bndrs id_bndrs '->' exp 
		{ Acon $1 $2 $3 $5 } 
	| lit '->' exp
		{ Alit $1 $3 }
	| '%_' '->' exp
		{ Adefault $3 }

lit	:: { Lit }
	: '(' INTEGER '::' aty ')'	{ Lint $2 $4 }
	| '(' RATIONAL '::' aty ')'	{ Lrational $2 $4 }
	| '(' CHAR '::' aty ')'		{ Lchar $2 $4 }
	| '(' STRING '::' aty ')'	{ Lstring $2 $4 }

tv_occ	:: { Var }
	: NAME	{ $1 }

q_var   :: { Qual Var }
        : modid '.' NAME	{ ($1, $3) }
        | NAME	                { ("", $1) } 

var_occ	:: { Var }
	: NAME	{ $1 }


-- Type constructor
q_tc_name	:: { Qual Tcon }
        : modid '.' CNAME	{ ($1, $3) }

-- Data constructor in a pattern or data type declaration
d_pat_occ :: { Qual Dcon }
        : modid '.' CNAME      { ($1, $3) }

-- Data constructor occurrence in an expression;
d_occ :: { Var }
       : CNAME { $1 }

{
tArrow :: Ty -> Ty -> Ty
tArrow t1 t2 = Tapp (Tapp (Tcon tcArrow) t1) t2

happyError :: P a 
happyError s l = failP (show l ++ ": Parse error") (take 100 s) l
}

