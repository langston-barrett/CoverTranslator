theory Merge = Main:

consts
  unitify    :: "'a list => 'a list list"
    (* turns a list into a list of singletons *)

  merge      :: "('a::linorder) list * 'a list => 'a list"
    (* merges two (ordered) lists *)

  mergesweep :: "('a::linorder) list list => 'a list list"
    (* merges neighbours in a list of lists (one pass) *)

  merging    :: "('a::linorder) list list => 'a list"
    (* applies mergesweep until only one list remains *)

  msort :: "('a::linorder) list => 'a list"
    (* composition of unitify and merging: sorts a list *)

text "Merge is an example of a simulatenously recursive functions
  where in each recursive call, one of the arguments is decreasing.
  Isabelle proves termination automatically when given the sum of the
  sizes of both arguments."

recdef merge "measure (%(xs,ys). length xs + length ys)"
"merge ([], ys) = ys"
"merge (xs, []) = xs"
"merge (x#xs, y#ys) = 
  (if x <= y then x # merge (xs, y#ys)
             else y # merge (x#xs, ys))"

text "Mergesweep is course-of-value recursive."

recdef mergesweep "measure length"
"mergesweep []          = []"
"mergesweep (xs#[])     = xs#[]"
"mergesweep (xs#ys#xss) = merge (xs, ys) # mergesweep xss"

text "The following lemma expresses that mergesweep is not increasing
  the length of its argument.  It is needed to proof merging
  terminating.  For some reasons unknown to me, the equivalent formulation
  length (mergesweep xss) <= length (xss) is not sufficient for the
  automated termination proof."

lemma length_mergesweep_ub' [simp]: 
  "length (mergesweep xss) < Suc (length xss)"
apply (induct_tac xss rule: mergesweep.induct)
apply (auto)
done

text "The recursion pattern of merging is 
  merging (_#_#xss) = merging (_ # mergesweep xss)."

recdef merging "measure length"
"merging []      = []"
"merging (xs#[]) = xs"
"merging xss = merging (mergesweep xss)"

primrec
"unitify [] = []"
"unitify (x#xs) = (x#[]) # unitify xs"

defs
  msort_def: "msort xs == merging (unitify xs)"


(********************************************************************)

section "Verification"

consts
  
  lb_head :: "('a::linorder) => 'a list => bool"

  ordered :: "('a::linorder) list => bool"

defs 
  lb_head_def: "lb_head a xs ==
    (case xs of [] => True | b#ys => a <= b)"

primrec 
"ordered [] = True"
"ordered (x#xs) = (lb_head x xs & ordered xs)"


text "merge preserves lower bounds"

lemma lb_head_merge': "lb_head a xs --> lb_head a ys --> 
  lb_head a (merge (xs, ys))"
apply (induct_tac xs ys rule: merge.induct)
apply (simp_all add: lb_head_def)
done

(* the version version with object implication was needed to do
induction, the second version with meta-implication is needed for
reuse in subsequent proofs *)

lemma lb_head_merge: "lb_head a xs ==> lb_head a ys ==> 
  lb_head a (merge (xs, ys))"
apply (simp_all add: lb_head_merge')
done


text "compatibility of lb_head with <="

lemma lb_head_trans: "x <= y ==> lb_head y ys ==> lb_head x (y#ys)"
apply (simp add: lb_head_def)
done


text "merge preserves order"

(* Proof : step case, case x <= y.
   Show  : ordered (x # merge (xs, y # ys)) 
   The part ordered (merge (xs, y # ys)) is by induction hypothesis,
   it remains to show that
     lb_head x (merge (xs, y # ys))
   apply lb_head_merge, we still need to establish
     lb_head x (y # ys)
   which amount to applying the hypothesis x <= y.
 *)

text "The completely automatic proof after induction and adding all
  properties of lb_head to the simplification set does not work, so we
  have to interact a little:"
 
lemma merge_ordered [simp]: "ordered xs --> ordered ys --> 
  ordered (merge (xs, ys))" 
apply (induct_tac xs ys rule: merge.induct)
   apply (simp_all)
apply (intro conjI impI)
 apply (rule lb_head_merge)
  apply (simp)
 apply (simp add: lb_head_def)
apply (rule lb_head_merge)
 apply (simp add: lb_head_def)
apply (simp)
done

text "The remaining steps are to show that both mergesweep and merging preserve order.  Then orderedness of a msorted list follows from orderedness of singleton lists."

lemma mergesweep_ordered [simp]: "list_all ordered xss --> list_all ordered (mergesweep xss)"
apply (induct_tac xss rule: mergesweep.induct)
apply (auto)
done

lemma mergesweep_ordered [simp]: "list_all ordered xss --> ordered (merging xss)"
apply (induct_tac xss rule: merging.induct)
apply (auto)
done

lemma unitify_ordered [simp]: "list_all ordered (unitify xs)"
apply (induct_tac xs)
apply (auto)
apply (simp add: lb_head_def)
done

text "Now we can tackle the partial correctness of msort."

theorem msort_ordered: "ordered (msort xs)" 
apply (simp add: msort_def)
done

end