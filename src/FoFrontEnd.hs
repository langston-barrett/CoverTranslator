{-| This module is used to produce FOL problems from a property and a set
    of libraries. Necessary lemmas and definitions from the libraries are
    kept and added as hypothesis to the problem, the rest is sliced away. -}

module FoFrontEnd (splitAndSlice) where
import Fol

data SliceMode = WithoutDef | WithDef

data LookupSide = DefLookup | PropLookup | PropNegLookup

defLookup :: [Fol.Def] -> String -> [Fol.Clause]
defLookup defs name = findAll [] defs
    where findAll [] [] = error ("definition " ++ name ++ " not found.")
	  findAll l  [] = l
	  findAll l ((Qname _ n,cl):t) | n == name = findAll (cl:l) t
	  findAll l (h:t) = findAll l t

follow :: [Fol.Library] -> [Fol.Clause] -> [Fol.Clause]
follow lib cls = 
    case cls of 
    [ClOr [ClInline (Qname m' name')]] -> libLookup PropLookup lib m' name'
    [ClOr [ClNinline (Qname m' name')]] -> libLookup PropNegLookup lib m' name'
    _ -> cls

propLookup :: [Fol.Library] -> [Fol.Prop] -> 
	      String -> ([Fol.Clause], [Fol.Clause])
propLookup lib props name =
    case props of
    [] -> error ("lemma " ++ name ++ " not found.")
    (Qname _ n, _, pcl, ncl):t | n == name -> (pcl', ncl')
			       where pcl' = follow lib pcl
				     ncl' = follow lib ncl
    h:t -> propLookup lib t name

libLookup :: LookupSide -> [Fol.Library] -> String -> String -> [Fol.Clause]
libLookup side lib m name = 
    case lib of
    [] -> 
	case side of 
	DefLookup -> []
	_ -> error ("module " ++ m ++ " not found.")
    (s,b,d,p):t | s == m ->
		  case side of
		  DefLookup -> if b then defLookup d name else []
		  PropLookup -> fst (propLookup lib p name)
		  PropNegLookup -> snd (propLookup lib p name) 
    h:t -> libLookup side t m name

slice :: [Fol.Library] -> Fol.Library -> Fol.Prop -> Fol.ProofObl
slice lib (mName,b,code,props) (propName,lemmas,propT,propF) = proofOb
    where proofOb = (propName,defCode++lemmaCode, prop)
          prop = 
              case propF of 
              [ClOr [ClInline  (Qname m n)]] -> libLookup PropLookup llib m n
              [ClOr [ClNinline (Qname m n)]] -> 
		  libLookup PropNegLookup llib m n
              _ -> propF
          defCode   = sliceCode lib (([],code),fv)
          lemmaCode = foldl findLemma [] lemmas
          findLemma code (Qname m n) = code ++ (libLookup PropLookup llib m n)
          llib = (mName,b,code,props):lib
          keep name ((kept,notYet),toVisit) (s,cl) = 
              if name == s then
                     ((cl:kept,notYet),fvClause s toVisit cl)
              else
                     ((kept,(s,cl):notYet),toVisit)
          filterV lib (Qname mname nname) toVisit lDef = 
	      case foldl (keep (Qname mname nname)) (([],[]),toVisit) lDef of 
	      (([], n), t) -> ((cls, n), t')
		  where cls = libLookup DefLookup lib mname nname
			t'  = foldl (fvClause (Qname mname nname)) t cls
	      ((cls,n),t) -> ((cls, n), t)
          sliceCode lib ((kept,notYet),toVisit) = 
              case toVisit of
              []   -> kept
              x:xs -> let ((k,n),t) = filterV lib x xs notYet in
                          sliceCode lib ((k++kept,n),t) 
          fv = foldl (fvClause propName) [] propF

splitAndSlice :: [Fol.Library] -> Fol.Library -> [Fol.ProofObl]
splitAndSlice lib (n, b, code, props) = map (slice lib (n,b,code,props)) props
