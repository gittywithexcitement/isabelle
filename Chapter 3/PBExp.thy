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
fun nnf_bad :: "pbexp \<Rightarrow> pbexp" where
  "nnf_bad (VAR x) = (VAR x)" |
(*   "nnf_bad (NOT b) = (
    case nnf_bad b of
      (NOT c)     \<Rightarrow> c |
      (AND b1 b2) \<Rightarrow> (OR   (nnf_bad (NOT b1)) (nnf_bad (NOT b2))) |
      (OR b1 b2)  \<Rightarrow> (AND  (nnf_bad (NOT b1)) (nnf_bad (NOT b2))) |
      (VAR c)     \<Rightarrow> NOT (VAR c))" |   *)
  "nnf_bad (NOT (VAR x)) = (NOT (VAR x))" |
  "nnf_bad (NOT (AND a b)) = OR (nnf_bad (NOT a)) (nnf_bad (NOT b))" |
  "nnf_bad (NOT (OR a b)) = AND (nnf_bad (NOT a)) (nnf_bad (NOT b))" |
  "nnf_bad (NOT (NOT b)) = nnf_bad b " |
  "nnf_bad (AND b1 b2) = (AND (nnf_bad b1) (nnf_bad b2))" |
  "nnf_bad (OR b1 b2) = (OR (nnf_bad b1) (nnf_bad b2))" 
    
(* https://github.com/cmr/ConcreteSemantics/blob/master/CS_Ch3.thy   *)
  
fun nnf_gh :: "pbexp \<Rightarrow> pbexp" where
  "nnf_gh (VAR x) = VAR x" |
  "nnf_gh (NOT (VAR x)) = (NOT (VAR x))" |
  "nnf_gh (NOT (AND a b)) = OR (nnf_gh (NOT a)) (nnf_gh (NOT b))" |
  "nnf_gh (NOT (OR a b)) = AND (nnf_gh (NOT a)) (nnf_gh (NOT b))" |
  "nnf_gh (NOT (NOT b)) = nnf_gh b " |
  "nnf_gh (AND a b) = AND (nnf_gh a) (nnf_gh b)" |
  "nnf_gh (OR a b) = OR (nnf_gh a) (nnf_gh b)"
  
    
    (* How many NOTs have been encountered so far, travelling from the expression's root to this point?
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
  by simp_all
    
    (* True when NOT is only applied to VARs. Otherwise, false.
What about not(not(var))? *)
fun is_nnf::"pbexp \<Rightarrow> bool"where
  "is_nnf (VAR x) = True" |
  "is_nnf (NOT b) = 
    (case b of
      (VAR _) \<Rightarrow> True|
      _       \<Rightarrow> False)" |
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"
  
value "is_nnf (VAR ''x'')"  
value "is_nnf (NOT(VAR x))"  
value "is_nnf (NOT(NOT(VAR x)))"
  
lemma nnf_returns_nnf_expression: "is_nnf (nnf exp num)"
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
qed
  
  (* Returns true if the expression is an OR   *)
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
  "is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"
  
(* args:
first child on an AND, already dnf'ed
second child on an AND, already dnf'ed
returns: the transformed expression; pulling ORs up through the parent AND as needed *)
fun transform_children_of_and :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"transform_children_of_and (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r) = 
  (OR (OR (AND or\<^sub>l\<^sub>l or\<^sub>r\<^sub>l) (AND or\<^sub>l\<^sub>l or\<^sub>r\<^sub>r)) (OR (AND or\<^sub>l\<^sub>r or\<^sub>r\<^sub>l) (AND or\<^sub>l\<^sub>r or\<^sub>r\<^sub>r)))"|
"transform_children_of_and (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) notOr =
  OR (AND or\<^sub>l\<^sub>l notOr) (AND or\<^sub>l\<^sub>r notOr)"|
"transform_children_of_and notOr (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r) =
  OR (AND or\<^sub>r\<^sub>l notOr) (AND or\<^sub>r\<^sub>r notOr)"|
"transform_children_of_and notOr\<^sub>l notOr\<^sub>r = AND notOr\<^sub>l notOr\<^sub>r"

value "transform_children_of_and (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r)"
value "transform_children_of_and (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (VAR ''y'')"
value "transform_children_of_and (VAR ''x'') (OR or\<^sub>r\<^sub>l or\<^sub>r\<^sub>r)"
value "transform_children_of_and (VAR ''x'') (VAR ''y'')"  (* This isn't being evaluated *)
  
(* The argument must be in NNF form (NOTs may only be applied to VAR, i.e. are at the leaves) 
 If the arg is in NNF form, then once we have moved up the tree past the VARs and NOTs, all that
 remains are ANDs and ORs.
 We would like to bubble up the ORs*)
fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = (VAR x)" |
  "dnf_of_nnf (NOT b) = NOT (dnf_of_nnf b)" |
  "dnf_of_nnf (AND b\<^sub>l b\<^sub>r) = 
    (let dnf_b\<^sub>l = dnf_of_nnf b\<^sub>l;
         dnf_b\<^sub>r = dnf_of_nnf b\<^sub>r
    in transform_children_of_and dnf_b\<^sub>l dnf_b\<^sub>r)" |
  "dnf_of_nnf (OR b1 b2) = (OR (dnf_of_nnf b1) (dnf_of_nnf b2))"

value "dnf_of_nnf (AND (OR or\<^sub>l\<^sub>l or\<^sub>l\<^sub>r) (VAR ''y''))"
  
lemma dnf_preserves_value:"pbval (dnf_of_nnf exp) s = pbval exp s"
proof(induction exp)
  case (VAR x)
  then show ?case by simp
next
  case (NOT exp)
  then show ?case by simp
next
  case (OR exp1 exp2)
  then show ?case by simp
next
  case (AND exp1 exp2)
  {
    fix dnf_exp1 dnf_exp2 
    assume fix1:"dnf_exp1 = dnf_of_nnf exp1" and fix2:"dnf_exp2 = dnf_of_nnf exp2"
    have "pbval (dnf_of_nnf (AND exp1 exp2)) s = pbval (transform_children_of_and (dnf_of_nnf exp1) (dnf_of_nnf exp2)) s"
      by simp 
    then have "... = pbval (transform_children_of_and dnf_exp1 dnf_exp2) s" 
      by (simp add: fix1 fix2)
    then have "pbval (transform_children_of_and dnf_exp1 dnf_exp2) s = pbval (AND exp1 exp2) s"
    proof(cases dnf_exp1)
      case v1:(VAR x1)
      then show ?thesis 
      proof(cases dnf_exp2)
        case (VAR x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) v1 fix1 fix2 by simp
      next
        case (NOT x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) v1 fix1 fix2 by simp
      next
        case (AND x31 x32)
        then show ?thesis
          using AND.IH(1) AND.IH(2) v1 fix1 fix2 by simp
      next
        case (OR x41 x42)
        then show ?thesis
          using AND.IH(1) AND.IH(2) v1 fix1 fix2 by auto
      qed
    next
      case n1:(NOT x1)
      then show ?thesis 
      proof(cases dnf_exp2)
        case (VAR x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) n1 fix1 fix2 by simp
      next
        case (NOT x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) n1 fix1 fix2 by simp
      next
        case (AND x31 x32)
        then show ?thesis
          using AND.IH(1) AND.IH(2) n1 fix1 fix2 by simp
      next
        case (OR x41 x42)
        then show ?thesis
          using AND.IH(1) AND.IH(2) n1 fix1 fix2 by auto
      qed
    next
      case a1:(AND x31 x32)
      then show ?thesis 
      proof(cases dnf_exp2)
        case (VAR x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) a1 fix1 fix2 by simp
      next
        case (NOT x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) a1 fix1 fix2 by simp
      next
        case (AND x31 x32)
        then show ?thesis
          using AND.IH(1) AND.IH(2) a1 fix1 fix2 by simp
      next
        case (OR x41 x42)
        then show ?thesis
          using AND.IH(1) AND.IH(2) a1 fix1 fix2 by auto
      qed
    next
      case o1:(OR x41 x42)
      then show ?thesis 
      proof(cases dnf_exp2)
        case (VAR x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) o1 fix1 fix2 by auto
      next
        case (NOT x2)
        then show ?thesis
          using AND.IH(1) AND.IH(2) o1 fix1 fix2 by auto
      next
        case (AND x31 x32)
        then show ?thesis
          using AND.IH(1) AND.IH(2) o1 fix1 fix2 by auto
      next
        case (OR x41 x42)
        then show ?thesis
          using AND.IH(1) AND.IH(2) o1 fix1 fix2 by auto
      qed
    qed
    then have ?case 
      by (simp add: fix1 fix2)
  }
  then show ?case
    by simp
qed
  
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
  then have "is_nnf (AND exp1 exp2)" (* sledgehammer *)
    (* then have "is_nnf exp1" sledgehammer *)
    
(* using this: *)
    (* is_dnf (dnf_of_nnf exp1) *)
    (* is_dnf (dnf_of_nnf exp2) *)
(* goal (1 subgoal): *)
 (* 1. is_dnf (dnf_of_nnf (AND exp1 exp2))     *)
    
  then show ?case 
    apply(simp)
    (* sledgehammer *)
 (* quickcheck[random] *)
 (* nitpick *)
        (* "is_dnf (AND b1 b2) _ = (is_dnf b1 SeenAnAnd \<and> is_dnf b2 SeenAnAnd)" | *)

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
    nitpick
    quickcheck[random]
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