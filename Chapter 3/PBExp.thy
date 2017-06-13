theory PBExp imports AExp begin
  
subsection "Boolean Expressions"
  
datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp
  
type_synonym bstate = "vname \<Rightarrow> bool"
  
fun pbval :: "pbexp \<Rightarrow> bstate \<Rightarrow> bool" where
  "pbval (VAR x) s = s x" |
  "pbval (NOT b) s = (\<not> pbval b s)" |
  "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
  "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"
  
subsection "Exercise 3.9"
  
lemma not_not_is_id[simp]: "pbval (NOT (NOT exp)) s = pbval exp s"
  apply(induction exp)
  by simp_all
    
lemma equal_implies_nots_equal:
  assumes "pbval e1 s = pbval e2 s"
  shows "pbval (NOT e1) s = pbval (NOT e2) s"
  by (simp add: assms)
    
text{* Optimizing constructors: *}
  
  (* remove extraneous NOTs, i.e. NOT(NOT(x)) = x *)
fun not_simp :: "pbexp \<Rightarrow> pbexp"where
  "not_simp (VAR x) = (VAR x)" |
  (* First recurse on b, then pattern match *)
  "not_simp (NOT b) = (
    case not_simp b of
      (NOT c) \<Rightarrow> c|
      _       \<Rightarrow> NOT b)" |
  "not_simp (AND b1 b2) = (AND (not_simp b1) (not_simp b2))" |
  "not_simp (OR b1 b2) = (OR (not_simp b1) (not_simp b2))"
  
value "not_simp (NOT (NOT exp))"
value "not_simp (NOT (NOT (NOT exp)))"
value "not_simp (NOT (NOT (NOT (NOT exp))))"
  
lemma not_preserves_value[simp]: "pbval (not_simp exp\<^sub>o) s = pbval exp\<^sub>o s"
  apply(induction exp\<^sub>o)
     apply simp_all
  apply(simp split: pbexp.splits)
  by auto
    
    (* This implementation could not even be auto-proved to terminate. *)
     (* Converts a pbexp into NNF by pushing NOT inwards as much as possible. *)
(* fun nnf_bad :: "pbexp \<Rightarrow> pbexp" where
  "nnf_bad (VAR x) = (VAR x)" |
   "nnf_bad (NOT b) = (
    case nnf_bad b of
      (NOT c)     \<Rightarrow> c |
      (AND b1 b2) \<Rightarrow> (OR   (nnf_bad (NOT b1)) (nnf_bad (NOT b2))) |
      (OR b1 b2)  \<Rightarrow> (AND  (nnf_bad (NOT b1)) (nnf_bad (NOT b2))) |
      (VAR c)     \<Rightarrow> NOT (VAR c))" |   
  "nnf_bad (AND b1 b2) = (AND (nnf_bad b1) (nnf_bad b2))" |
  "nnf_bad (OR b1 b2) = (OR (nnf_bad b1) (nnf_bad b2))"  *)
    
(* https://github.com/cmr/ConcreteSemantics/blob/master/CS_Ch3.thy   *)
 
    (* matches GH *)
fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = VAR x" |
  "nnf (NOT (VAR x)) = (NOT (VAR x))" |
  "nnf (NOT (NOT b)) = nnf b " |
  "nnf (NOT (AND a b)) = OR (nnf (NOT a)) (nnf (NOT b))" |
  "nnf (NOT (OR a b)) = AND (nnf (NOT a)) (nnf (NOT b))" |
  "nnf (AND a b) = AND (nnf a) (nnf b)" |
  "nnf (OR a b) = OR (nnf a) (nnf b)"
  
    
(*     (* How many NOTs have been encountered so far, travelling from the expression's root to this point?
Every time two NOTs are encountered, the count is reset to zero. *)
datatype num_nots = ZeroN | OneN  
  
  (* Convert an expression to negative normal form; pass it ZeroN to begin with   *)
fun nnf :: "pbexp \<Rightarrow> num_nots \<Rightarrow> pbexp" where
  "nnf (VAR x) ZeroN = (VAR x)" |
  "nnf (VAR x) OneN = NOT (VAR x)" |
  "nnf (NOT b) ZeroN = nnf b OneN" |
  "nnf (NOT b) OneN = nnf b ZeroN" |
  "nnf (AND b1 b2) ZeroN = (AND (nnf b1 ZeroN) (nnf b2 ZeroN))" |
  "nnf (AND b1 b2) OneN = (OR (nnf b1 OneN) (nnf b2 OneN))" |
  "nnf (OR b1 b2) ZeroN = (OR (nnf b1 ZeroN) (nnf b2 ZeroN))" |
  "nnf (OR b1 b2) OneN = (AND (nnf b1 OneN) (nnf b2 OneN))"
  
value "nnf (NOT (NOT (VAR ''x''))) ZeroN"
value "nnf (NOT (NOT (NOT (VAR ''x'')))) ZeroN"
value "nnf (NOT (NOT (NOT (NOT (VAR ''x''))))) ZeroN"
  
lemma nnf_preserves_value: 
  "pbval (nnf exp num) s = 
    (case num of ZeroN \<Rightarrow> pbval exp s | OneN \<Rightarrow> (\<not> pbval exp s))"
  apply(simp split: num_nots.splits)
  apply(induction exp arbitrary:num)
  by simp_all *)
  
lemma nnf_preserves_value:"pbval (nnf exp) s = pbval exp s"
  apply(induction rule: nnf.induct)
  by simp_all
    
    (* True when NOT is only applied to VARs. Otherwise, false.
What about not(not(var))? *)
fun is_nnf::"pbexp \<Rightarrow> bool"where
  "is_nnf (VAR x) = True" |
  "is_nnf (NOT (VAR _)) = True" |
  "is_nnf (NOT _) = False" |
(*   "is_nnf (NOT (VAR _)) = True" |
  "is_nnf (NOT _) = False" | *)
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"
  
value "is_nnf (VAR ''x'')"  
value "is_nnf (NOT(VAR x))"  
value "is_nnf (NOT(NOT(VAR x)))"
  
(* lemma nnf_returns_nnf_expression: "is_nnf (nnf exp num)"
proof(induction exp arbitrary:num)
  case (VAR x)
  then show ?case
  proof(induction num)
    case ZeroN
    then show ?case by simp
  next
    case OneN
    then show ?case by simp
  qed
next
  case (AND exp1 exp2)
  then show ?case
  proof(induction num)
    case ZeroN
    then show ?case by simp
  next
    case OneN
    then show ?case by simp
  qed
next
  case (OR exp1 exp2)
  then show ?case
  proof(induction num)
    case ZeroN
    then show ?case by simp
  next
    case OneN
    then show ?case by simp
  qed
next
  case (NOT exp)
  then show ?case
  proof(induction num)
    case ZeroN
    then show ?case by simp
  next
    case OneN
    then show ?case by simp
  qed
qed *)
  
  (* NB: when using 'rule: nnf.induct', you MUST specify the induction variable! *)
lemma nnf_returns_nnf_expression: "is_nnf (nnf exp)"
  (* 4. \<And>a b. is_nnf (NOT a) \<Longrightarrow> is_nnf (NOT b) \<Longrightarrow> is_nnf (NOT (AND a b)) *)
  (* apply(induction rule: nnf.induct) (* Was creating FALSE goals *) *)
  
    (* 4. \<And>a b. is_nnf (nnf (NOT a)) \<Longrightarrow> is_nnf (nnf (NOT b)) 
\<Longrightarrow> is_nnf (nnf (NOT (AND a b))) *)
  apply(induction exp rule: nnf.induct)
  by simp_all
 
(*   (* Returns true if the expression is an OR   *)
fun is_OR :: "pbexp \<Rightarrow> bool" where  
  "is_OR (OR _ _) = True" |
  "is_OR _ = False"
  
  (* No ANDs have been seen yet (when traversing the tree from root to here)
| at least one AND has been seen. *)
datatype seen_and = NeverSeenAnd | SeenAnAnd  
  
  (* An expression is in DNF (disjunctive normal form) if it is in NNF and if no OR occurs below an
AND.*)
fun is_dnf:: "pbexp \<Rightarrow> bool"where
  "is_dnf (VAR _) = True" |
  "is_dnf (NOT b) = is_dnf b"|
  "is_dnf (AND b1 b2) = (is_dnf b1 \<and> is_dnf b2 \<and> (\<not> is_OR b1) \<and> (\<not> is_OR b2))" |
  "is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)" *)
  
  (* An expression is in DNF (disjunctive normal form) if it is in NNF and if no OR occurs below an
AND.*)
fun is_dnf:: "pbexp \<Rightarrow> bool"where
  "is_dnf (VAR _) = True" |
  "is_dnf (NOT b) = is_dnf b"|
  "is_dnf (AND (OR _ _) _) = False" |
  "is_dnf (AND _ (OR _ _)) = False" |
  "is_dnf (AND bl br) = (is_dnf bl \<and> is_dnf br)" |
  "is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"
  
(* The argument must be in NNF form (NOTs may only be applied to VAR, i.e. are at the leaves) 
 If the arg is in NNF form, then once we have moved up the tree past the VARs and NOTs, all that
 remains are ANDs and ORs.
 We would like to bubble up the ORs*)
(* fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = (VAR x)" |
 
  (* No need to recurse inside NOT, because arg is already in NNF form *)
  (* "dnf_of_nnf (NOT b) = NOT (dnf_of_nnf b)" | *)
  "dnf_of_nnf (NOT b) = NOT b" |
 
  "dnf_of_nnf (OR b1 b2) = (OR (dnf_of_nnf b1) (dnf_of_nnf b2))"|
 
(*   I think this is wrong; needs to recurse on children of AND before 
  pattern matching on those transformed children *)
  "dnf_of_nnf (AND (OR ll lr) (OR rl rr)) = 
    OR (OR (AND ll rl) (AND ll rr)) (OR (AND lr rl) (AND lr rr))"|
  "dnf_of_nnf (AND (OR ll lr) r) = (OR (AND ll r) (AND lr r))"|
  "dnf_of_nnf (AND l (OR rl rr)) = (OR (AND l rl) (AND l rr))"|
  "dnf_of_nnf (AND l r) = AND (dnf_of_nnf l) (dnf_of_nnf r)" *)
  
(* Before adding extra recursion   *)
(* args:
first child on an AND, already dnf'ed
second child on an AND, already dnf'ed
returns: the transformed expression; pulling ORs up through the parent AND as needed *)
(* fun push_and_below_or :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"push_and_below_or (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r) = 
  (OR (OR (AND or\<^sub>l\<^sub>l or\<^sub>r\<^sub>l) (AND or\<^sub>l\<^sub>l or\<^sub>r\<^sub>r)) (OR (AND or\<^sub>l\<^sub>r or\<^sub>r\<^sub>l) (AND or\<^sub>l\<^sub>r or\<^sub>r\<^sub>r)))"|
"push_and_below_or (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) notOr =
  OR (AND or\<^sub>l\<^sub>l notOr) (AND or\<^sub>l\<^sub>r notOr)"|
"push_and_below_or notOr (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r) =
  OR (AND or\<^sub>r\<^sub>l notOr) (AND or\<^sub>r\<^sub>r notOr)"|
"push_and_below_or notOr\<^sub>l notOr\<^sub>r = AND notOr\<^sub>l notOr\<^sub>r" *)
  
(* TODO I think I need a new function: push AND down, that pushes AND down below all OR
children. push_and_below_or is halfway there. *) 
  (* Push AND down:
when encountering an AND above an OR (in dnf_of_nnf), this function is called.
It recursively pushes down AND until a AND, NOT, or VAR is found.
It converts a
       and
     or   or
into:
        or
    or      or
 and and and and 
Then it recurses on the 4 AND's that were just created, because there may be ORs beneath them.
 *)
  
(* args:
first child on an AND, already dnf'ed
second child on an AND, already dnf'ed
returns: the transformed expression; pushing an AND below its OR children (if there are any). This
function will recursively call itself until all ORs have been moved above the ANDs.

Because dnf_of_nnf is this function's only caller, and dnf_of_nnf recurses on the children of an AND
before calling this function, we know that we may stop once we encounter an AND, NOT, or VAR.*)
fun push_and_below_or :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"push_and_below_or (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r) = 
  (OR (OR (push_and_below_or or\<^sub>l\<^sub>l or\<^sub>r\<^sub>l) (push_and_below_or or\<^sub>l\<^sub>l or\<^sub>r\<^sub>r)) 
      (OR (push_and_below_or or\<^sub>l\<^sub>r or\<^sub>r\<^sub>l) (push_and_below_or or\<^sub>l\<^sub>r or\<^sub>r\<^sub>r)))"|
(* NB: the order of arguments to the recursive calls to push_and_below_or, found below, are
critical. For example, changing (push_and_below_or or\<^sub>l\<^sub>l notOr) to (push_and_below_or notOr or\<^sub>l\<^sub>l)
will cause auto-termination proof of this function to fail.*)
"push_and_below_or (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) notOr =
  OR (push_and_below_or or\<^sub>l\<^sub>l notOr) (push_and_below_or or\<^sub>l\<^sub>r notOr)"|
"push_and_below_or notOr (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r) =
  OR (push_and_below_or notOr or\<^sub>r\<^sub>l) (push_and_below_or notOr or\<^sub>r\<^sub>r)"|
"push_and_below_or notOr\<^sub>l notOr\<^sub>r = AND notOr\<^sub>l notOr\<^sub>r"  
 
value "push_and_below_or (OR (VAR ''1'') (OR (VAR ''2'') (VAR ''3''))) (OR (VAR ''4'') (VAR ''5''))"
value "push_and_below_or (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (VAR ''y'')"
value "push_and_below_or (VAR ''x'') (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r)"
value "push_and_below_or (VAR ''x'') (VAR ''y'')"
  
lemma push_and_below_or_preserves_eval:"pbval (push_and_below_or el er) s = pbval (AND el er) s"
  apply(induction el er rule: push_and_below_or.induct)
                      apply(simp_all)
  by auto

lemma push_and_below_or_preserves_nnf:"is_nnf el \<Longrightarrow> is_nnf er \<Longrightarrow> is_nnf (push_and_below_or el er)"
  apply(induction el er rule: push_and_below_or.induct)
  by (simp_all)

lemma push_and_below_or_preserves_dnf:
  "is_dnf el \<Longrightarrow> is_dnf er \<Longrightarrow> is_dnf (push_and_below_or el er)"
  apply(induction el er rule: push_and_below_or.induct)
  by (simp_all)

(* The argument must be in NNF form (NOTs may only be applied to VAR, i.e. are at the leaves) 
 If the arg is in NNF form, then once we have moved up the tree past the VARs and NOTs, all that
 remains are ANDs and ORs.
 We would like to bubble up the ORs*)
fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = (VAR x)" |
  (* No need to recurse inside the NOT because we know it's in NNF form. *)
  "dnf_of_nnf (NOT b) = NOT b" |
  "dnf_of_nnf (AND b\<^sub>l b\<^sub>r) = 
    (let dnf_b\<^sub>l = dnf_of_nnf b\<^sub>l;
         dnf_b\<^sub>r = dnf_of_nnf b\<^sub>r
    in push_and_below_or dnf_b\<^sub>l dnf_b\<^sub>r)" |
  "dnf_of_nnf (OR b1 b2) = (OR (dnf_of_nnf b1) (dnf_of_nnf b2))"
  
value "dnf_of_nnf (AND (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (VAR ''y''))"
  
lemma dnf_preserves_value[simp]:"pbval (dnf_of_nnf exp) s = pbval exp s"
  apply(induction exp)
     apply(simp_all)
  using push_and_below_or_preserves_eval by simp
    
lemma dnf_of_nnf_returns_dnf_1:"is_nnf exp \<Longrightarrow> is_dnf (dnf_of_nnf exp)"
  apply(induction exp rule: dnf_of_nnf.induct)
     apply(simp_all)
  using is_nnf.elims(2) apply fastforce
 (* using push_and_below_or_preserves_dnf sledgehammer[timeout=120] *)
proof - 
  fix b\<^sub>l b\<^sub>r
  {
    assume "is_dnf (dnf_of_nnf b\<^sub>l)" and "is_dnf (dnf_of_nnf b\<^sub>r)"
      and "is_nnf b\<^sub>l \<and> is_nnf b\<^sub>r"
    then have "is_dnf (push_and_below_or (dnf_of_nnf b\<^sub>l) (dnf_of_nnf b\<^sub>r))"
      using push_and_below_or_preserves_dnf by simp
  }
  then show "is_dnf (push_and_below_or (dnf_of_nnf b\<^sub>l) (dnf_of_nnf b\<^sub>r))"
    try
      (* try0 *)
      (* sledgehammer *)
      (* sorry *)
qed  
  oops
    

lemma dnf_of_nnf_returns_is_dnf:
  assumes "is_nnf exp"
  shows "is_dnf (dnf_of_nnf exp)" (* Might need to generalize NeverSeenAnd *)
proof(induction exp)
  case (VAR x)
  then show ?case 
    by simp
next
  case (NOT exp)
  then show ?case 
    by simp
next
  case (OR exp1 exp2)
  then show ?case 
    by simp
next
  case (AND exp1 exp2)
    
(* Nitpick found a counterexample:
 
  Free variables:
    exp = OR (VAR s\<^sub>1) (VAR s\<^sub>1)
    exp1 = VAR s\<^sub>1
    exp2 = VAR s\<^sub>1
  Skolem constants:
    exp1 = OR (OR (VAR s\<^sub>1) (VAR s\<^sub>1)) (OR (VAR s\<^sub>1) (VAR s\<^sub>1))
    exp2 = VAR s\<^sub>1 *)    
    
   
 (* nitpick *)
 (* quickcheck[random] *)
    (* exp = AND (OR (VAR [CHR 0xDC]) (VAR [CHR 0x91])) (VAR [CHR 0x7F, CHR 0xFD]) *)
    (* exp1__ = AND (OR (VAR [CHR ''I'', CHR 0xFA]) (VAR [])) (AND (VAR [CHR 0xA0]) (VAR [])) *)
    (* exp2__ = NOT (VAR [CHR 0x1F]) *)
    (* exp1 = OR (OR (VAR [CHR 0x9D, CHR ''9'']) (VAR [CHR ''-'', CHR 0x7F])) (VAR []) *)
    (* exp2 = OR (NOT (VAR [CHR 0xE6])) (AND (VAR [CHR 0x07]) (VAR ''d,'')) *)
       
  then show ?case 
  qed
  oops
    
lemma dnf_of_nnf_returns_is_dnf_1:
  assumes "is_nnf exp"
  shows "is_nnf exp \<Longrightarrow> is_dnf (dnf_of_nnf exp)" (* Might need to generalize NeverSeenAnd *)
proof(induction exp)
  case (VAR x)
  then show ?case 
    by simp
next
  case (NOT exp)
  then show ?case
    by (metis dnf_of_nnf.simps(2) is_OR.simps(1) is_OR.simps(3) is_dnf.elims(3) is_nnf.elims(3) is_nnf.simps(2) pbexp.distinct(7) pbexp.inject(2) pbexp.simps(18) pbexp.simps(19) pbexp.simps(20))
next
  case (AND exp1 exp2)
    (* is_nnf exp *)
    (* is_nnf (AND exp1 exp2) *)
    (* is_nnf exp1 \<Longrightarrow> is_dnf (dnf_of_nnf exp1) *)
    (* is_nnf exp2 \<Longrightarrow> is_dnf (dnf_of_nnf exp2) *)
    
    (* ?case \<equiv> is_dnf (dnf_of_nnf (AND exp1 exp2)) *)
 
  then show ?case 
    (* nitpick *)
    (* quickcheck[random] *)
(*         Free variables:
    exp1 = OR (OR (VAR s\<^sub>1) (VAR s\<^sub>1)) (OR (VAR s\<^sub>1) (VAR s\<^sub>1))
    exp2 = VAR s\<^sub>1 *)
      sorry
next
  case (OR exp1 exp2)
  then show ?case 
    by simp
qed    
  
(* is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b) *)
end
