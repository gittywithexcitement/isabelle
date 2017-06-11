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

(* How many NOTs have been encountered so far, travelling from the expression's root to this point?
Every time two NOTs are encountered, the count is reset to zero. *)
datatype num_nots = ZeroN | OneN  
  
(* Uses num_nots to simplify an expression's NOTs.   *)
fun nnf_v2 :: "pbexp \<Rightarrow> num_nots \<Rightarrow> pbexp" where
  "nnf_v2 (VAR x) ZeroN = (VAR x)" |
  "nnf_v2 (VAR x) OneN = NOT (VAR x)" |
  "nnf_v2 (NOT b) ZeroN = nnf_v2 b OneN" |
  "nnf_v2 (NOT b) OneN = nnf_v2 b ZeroN" |
  "nnf_v2 (AND b1 b2) ZeroN = (AND (nnf_v2 b1 ZeroN) (nnf_v2 b2 ZeroN))" |
  "nnf_v2 (AND b1 b2) OneN = (OR (nnf_v2 b1 OneN) (nnf_v2 b2 OneN))" |
  "nnf_v2 (OR b1 b2) ZeroN = (OR (nnf_v2 b1 ZeroN) (nnf_v2 b2 ZeroN))" |
  "nnf_v2 (OR b1 b2) OneN = (AND (nnf_v2 b1 OneN) (nnf_v2 b2 OneN))"

value "nnf_v2 (NOT (NOT (VAR ''x''))) ZeroN"
value "nnf_v2 (NOT (NOT (NOT (VAR ''x'')))) ZeroN"
value "nnf_v2 (NOT (NOT (NOT (NOT (VAR ''x''))))) ZeroN"
  
(* lemma nnf_v2_one_is_not: 
  "pbval (nnf_v2 exp ZeroN) s = pbval exp s 
  \<Longrightarrow> pbval (nnf_v2 exp OneN) s = (\<not> pbval exp s)"
  apply(induction exp)
    apply(simp_all)
 *)

(* lemma nnf_v2_preserves_value_1[simp]: 
  "pbval (nnf_v2 exp num) s = 
  (case num of ZeroN \<Rightarrow> pbval exp s | OneN \<Rightarrow> (\<not> pbval exp s))"
  (* apply(induction exp) *)
 apply(induction exp arbitrary:num)
    (* apply auto *)
    apply(simp split: num_nots.splits)
 *)
(* lemma nnf_v2_preserves_value_1: 
  "pbval (nnf_v2 exp num) s = 
  (case num of ZeroN \<Rightarrow> pbval exp s | OneN \<Rightarrow> (\<not> pbval exp s))"
proof(induction exp arbitrary:num)
  case (VAR x)
  then show ?case 
    by (simp split: num_nots.splits) 
next
  case (NOT exp)
  then show ?case 
    by (simp split: num_nots.splits) 
next
  case (AND exp1 exp2)
  then show ?case 
    by (simp split: num_nots.splits) 
next
  case (OR exp1 exp2)
  then show ?case 
    by (simp split: num_nots.splits) 
qed *)

(* lemma nnf_v2_preserves_value_2: 
  "pbval (nnf_v2 exp num) s = 
  (case num of ZeroN \<Rightarrow> pbval exp s | OneN \<Rightarrow> (\<not> pbval exp s))"
  apply(induction exp arbitrary:num)
     apply(simp split: num_nots.splits)
    apply(metis PBExp.nnf_v2_preserves_value_1)
   apply(metis PBExp.nnf_v2_preserves_value_1)
  apply(metis PBExp.nnf_v2_preserves_value_1) *)
    
lemma nnf_v2_preserves_value: 
  "pbval (nnf_v2 exp num) s = 
  (case num of ZeroN \<Rightarrow> pbval exp s | OneN \<Rightarrow> (\<not> pbval exp s))"
  apply(simp split: num_nots.splits)
  apply(induction exp arbitrary:num)
  by simp_all

  (* Do I need to generalize ZeroN to a variable? *)
(*  lemma nnf_v2_preserves_value[simp]: "pbval (nnf_v2 exp ZeroN) s = pbval exp s"
  apply(induction exp)
  (* apply(induction rule: nnf_v2.induct) *)
    apply simp_all
  apply(simp split: pbexp.splits) *)

 
fun is_var::"pbexp \<Rightarrow> bool"  where
  "is_var (VAR _) = True"|
  "is_var _ = False"
  
  (* True when NOT is only applied to VARs. Otherwise, false.
What about not(not(var))? *)
fun is_nnf::"pbexp \<Rightarrow> bool"where
  "is_nnf (VAR x) = True" |
  "is_nnf (NOT b) = is_var b" |
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"
  
value "is_nnf (VAR ''x'')"  
value "is_nnf (NOT(VAR x))"  
value "is_nnf (NOT(NOT(VAR x)))"

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
  "nnf (OR b1 b2) = (OR (nnf b1) (nnf b2))"
(*       (AND b1 b2) \<Rightarrow> (OR   (nnf (NOT b1)) (nnf (NOT b2))) |
      (OR b1 b2)  \<Rightarrow> (AND  (nnf (NOT b1)) (nnf (NOT b2))) |*)  
lemma nnf_preserves_value[simp]: "pbval (nnf exp\<^sub>o) s = pbval exp\<^sub>o s"
  apply(induction exp\<^sub>o arbitrary: s) 
     apply simp_all
  nitpick
  apply(simp split: pbexp.splits)
  by auto
    
lemma nnf_is_nnf: "is_nnf (nnf b)"
  apply(induction b)
    nitpick
       apply(simp_all)
      nitpick
  apply(simp split: pbexp.splits)
  nitpick *)

end