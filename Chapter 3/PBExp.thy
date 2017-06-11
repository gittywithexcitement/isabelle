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
(* (* Converts a pbexp into NNF by pushing NOT inwards as much as possible. *)
fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = (VAR x)" |
  "nnf (NOT b) = (
    case nnf b of
      (NOT c)     \<Rightarrow> c |
      (AND b1 b2) \<Rightarrow> (OR   (nnf (NOT b1)) (nnf (NOT b2))) |
      (OR b1 b2)  \<Rightarrow> (AND  (nnf (NOT b1)) (nnf (NOT b2))) |
      (VAR c)     \<Rightarrow> NOT (VAR c))" |  
  "nnf (AND b1 b2) = (AND (nnf b1) (nnf b2))" |
  "nnf (OR b1 b2) = (OR (nnf b1) (nnf b2))" *)    

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

end