module FolPP where

import Text.PrettyPrint.HughesPJ
import Fol
--import Cl.Print(printTree)


-- The debugging pretty printer
--debugPrinter :: ProofObl -> Doc
debugPrinter (_n,cs,p) = complete_doc
    where complete_doc = header $+$ transd $+$ 
                         middle $+$ transp $+$ 
                         footer
          header = text "-- Start of program: " -- <> text (opId n)
          middle = text "-- Properties"
          footer = text "-- End of file"
          transd = vcat (map (\ c -> (opClause c) <> (char '.')) cs)
          transp = vcat (map (\ c -> (opClause c) <> (char '.')) p)


instance Show Clause where
  show     = render . opClause
  showList = (++) . render . vcat . map (\c-> opClause c <> char '.')

-- The Otter pretty printer
otterPrinter :: ProofObl -> Doc
otterPrinter (n,cs,p) = complete_doc
    where complete_doc = header $+$ transd $+$ 
                         middle $+$ transp $+$ footer
          transd = vcat (map (\ c -> (opClause c) <> (char '.')) cs)
          transp = vcat (map (\ c -> (opClause c) <> (char '.')) p)
          header = vcat (map text [ "set(prolog_style_variables).",
                                    "set(auto).",
                                    "",
                                    "list(usable).",
                                    "",
                                    "equal(X,X).",
                                    "" ])
          middle = vcat (map text [ "",
                                    "end_of_list.",
                                    "",
                                    "list(sos).",
                                    "" ])
          footer = vcat (map text [ "",
                                    "end_of_list." ])

opClause :: Clause -> Doc
opClause cl = case cl of
    Cl cl                 -> opYes <> (opClBody cl)
    ClNot cl              -> opNot <> (opClBody cl)
    ClOr cs               -> hsep (punctuate (text "| ") (map opClause cs))
    ClInline id           -> error "Inlining not done"
    ClNinline (Qname m n) -> error ("Ninlining not done - "++m++"."++n)

opClBody :: ClBody -> Doc 
opClBody (ClEqual t1 t2) = opEqual <> 
                           (parens ((opTerm t1) <> comma <+> (opTerm t2)))

opTerm :: Term -> Doc
opTerm t = case t of
    Fvar s     -> text ("V_" ++ opId s)
    Ffun s     -> text ("f_" ++ opId s)
    Fcon s     -> text ("c_" ++ opId s)
    Fapp t1 t2 -> opApp <> (parens ((opTerm t1) <> comma <+> (opTerm t2)))

opId :: Id -> String
opId (Qname m v) = m ++ "_" ++ v

opApp :: Doc 
opApp = text "app"

opEqual :: Doc
opEqual = text "equal"

opNot :: Doc
opNot = text "-"

opYes :: Doc
opYes = empty

-- The TPTP pretty printer
tptpPrinter :: ProofObl -> Doc
tptpPrinter (n,cs,ps) = complete_doc -- Not implemented!
    where complete_doc = header $+$ footer
          header       = vcat (map text [ "" ])
          footer       = vcat (map text [ "" ])

tpTopLevelClause :: Clause -> Doc
tpTopLevelClause cl = intro <> transl <> (text " ]") $+$ outro
    where intro  = (text "input_clause(x,axiom,") $+$ (text " [ ")
          outro  = (text ").") $+$ (text "")
          transl = tpClause cl
 
tpClause :: Clause -> Doc
tpClause cl = case cl of
    Cl cl    -> tpYes <> (tpClBody cl)
    ClNot cl -> tpNot <> (tpClBody cl)
    ClOr cs  -> hsep (punctuate comma (map tpClause cs))

tpClBody :: ClBody -> Doc 
tpClBody (ClEqual t1 t2) = tpEqual <> 
                           (parens ((tpTerm t1) <> comma <+> (tpTerm t2)))

tpTerm :: Term -> Doc
tpTerm t = case t of
    Fvar s     -> text ("V_" ++ tpId s)
    Ffun s     -> text ("f_" ++ tpId s)
    Fcon s     -> text ("c_" ++ tpId s)
    Fapp t1 t2 -> redApp [tpTerm t2] t1
        where redApp ds (Fapp t1' t2') = redApp ((tpTerm t2'):ds) t1'
              redApp ds t = (tpTerm t) <> (parens(hcat (punctuate comma ds)))

tpId :: Id -> String
tpId (Qname m v) = m ++ "_" ++ v

tpApp :: Doc 
tpApp = empty

tpEqual :: Doc
tpEqual = text "equal"

tpNot :: Doc
tpNot = text "--"

tpYes :: Doc
tpYes = text "++"
