theory unique
  imports Main   
  "~~/src/HOL/Library/Code_Target_Nat"
  (* "~~/src/HOL/Library/Fset" *)
  "~~/src/HOL/Library/Finite_Set"
begin

section \<open>define unique\<close>
  
(* unique. Takes a sequence of integers, returns the unique elements of that
list. There is no requirement on the ordering of the returned values. 

inspired by https://www.hillelwayne.com/post/theorem-prover-showdown/ *)

fun uniqueAccum :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "uniqueAccum [] accum = accum" |
  "uniqueAccum (x # xs) accum = uniqueAccum xs (List.insert x accum)"
(* note that List.insert uses set *) 

fun unique :: "nat list => nat list" where
  "unique xs = uniqueAccum xs []"

fun uniqueAccumS :: "nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> nat list" where
  "uniqueAccumS [] accum accumSet = accum" |
  "uniqueAccumS (x # xs) accum accumSet = 
    (if x \<in> accumSet then (uniqueAccumS xs accum accumSet) else (uniqueAccumS xs (x # accum) (insert x accumSet)))" 

fun uniqueS :: "nat list => nat list" where
  "uniqueS xs = uniqueAccumS xs [] {}"

(* Prove: 

All elements of the original list are in the output

Every element of the output is distinct

Note from webpage author:

I specified that all elements of the original list are in the output, but not
that all elements of the output were in the original list. If the method took
in [1, 2, 2] and returned [1, 2, 99], it would still pass the partial
specification. I really dropped the ball on this one. *)

section \<open>Proofs\<close>

subsection \<open>All elements of the original list are elements of the output\<close>

text "prefix of result is the list"

lemma uniqueAccum_in_accum:
  "y\<^sub>e \<in> set ys
  \<Longrightarrow> y\<^sub>e \<in> set (uniqueAccum xs ys)"
  apply(induction xs arbitrary: ys)
  by auto

lemma uniqueAccum_in_lst:
  "x\<^sub>e \<in> set xs
  \<Longrightarrow> x\<^sub>e \<in> set (uniqueAccum xs ys)"
  apply(induction xs arbitrary: ys)
   apply auto
  using uniqueAccum_in_accum by auto

(*TODO delete unused? *)
lemma uniqueAccum_add_one:
  "y \<in> set (uniqueAccum [] ys)
  \<Longrightarrow> y \<in> set (uniqueAccum [x] ys)"
  by simp

lemma uniqueAccum_add_many:
  shows "y\<^sub>e \<in> set (uniqueAccum [] ys)
      \<Longrightarrow> y\<^sub>e \<in> set (uniqueAccum xs ys)"
  apply(induction xs arbitrary: ys)
  by auto

lemma uniqueAccum_reversible:
  shows "a \<in> set (uniqueAccum [] xs)
      \<Longrightarrow> a \<in> set (uniqueAccum [] (rev xs))"
  by auto

lemma uniqueAccum_set_union:
  shows "set (uniqueAccum xs ys) = set xs \<union> set ys"
  apply(induction xs arbitrary: ys)
  by auto

lemma uniqueAccum_in_one_of:
  shows "a \<in> set (uniqueAccum xs ys) \<Longrightarrow> a \<in> set xs \<or> a \<in> set ys"
  by (simp add: uniqueAccum_set_union)

lemma uniqueAccum_add_to_accum:
  shows "a \<in> set (uniqueAccum xs []) 
  \<Longrightarrow> a \<in> set (uniqueAccum xs [y])"
  using uniqueAccum_add_many uniqueAccum_in_lst uniqueAccum_in_one_of by blast

lemma uniqueAccum_order_invariant:
  shows "a \<in> set (uniqueAccum xs ys) \<Longrightarrow> a \<in> set (uniqueAccum ys xs)"
  using uniqueAccum_in_accum uniqueAccum_in_lst uniqueAccum_in_one_of by blast

(* https://isabelle.in.tum.de/community/FAQ#There_are_lots_of_arrows_in_Isabelle.2FHOL._What.27s_the_difference_between_-.3E.2C_.3D.3E.2C_--.3E.2C_and_.3D.3D.3E_.3F *)

lemma all_elements_present:
  fixes xs :: "nat list"
  assumes "x \<in> set xs"
  shows "x \<in> set xs \<Longrightarrow> x \<in> set (unique xs)"
  by (simp add: uniqueAccum_in_lst)

lemma all_elements_present1:
  fixes xs :: "nat list"
  assumes "x \<in> set xs"
  shows "\<forall> x. x \<in> set xs \<Longrightarrow> x \<in> set (unique xs)"
proof(induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then show ?case
    apply simp_all
    oops

(* I think this is wrong. prog-prove.pdf says:
"The implication =\<Rightarrow> is part of the Isabelle framework..."
*)
lemma all_elements_present2:
  fixes xs :: "nat list"
  assumes "x \<in> set xs"
  shows "\<forall> x. x \<in> set xs \<longrightarrow> x \<in> set (unique xs)" 
proof(induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then show ?case
   apply simp_all
    oops