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

lemma uniqueAccum_add_to_accum:
  shows "a \<in> set (uniqueAccum xs []) 
  \<Longrightarrow> a \<in> set (uniqueAccum xs [y])"
(*   apply(induction xs)
   apply auto *)
proof(cases "a = y")
  case True
  then show ?thesis 
    by (simp add: uniqueAccum_in_accum)
next
  case False
  have "a \<in> set (uniqueAccum xs [])" nitpick
  then show ?thesis nitpick
qed oops

(* if x \<in> set xs then xs else x # xs *)

lemma uniqueAccum_order_invariant:
  shows "a \<in> set (uniqueAccum xs ys) \<Longrightarrow> a \<in> set (uniqueAccum ys xs)"
proof(induction xs arbitrary: ys)
  case Nil
  then show ?case 
  proof(induction ys)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys\<^sub>p)
    then show ?case
    proof(cases "a = y")
      case True
      then show ?thesis
        by (simp add: uniqueAccum_in_accum)
    next
      case False
       show ?thesis         
        by (metis Cons.prems uniqueAccum.simps(1) uniqueAccum_in_lst)
    qed
  qed
next
  case consxs:(Cons x xs\<^sub>p)
  then show ?case 
  proof(induction ys)
    case Nil
    then show ?case 
      by fastforce
  next
    case consys:(Cons y ys\<^sub>p)
    then show ?case
    proof(cases "a = y")
      case True
      then show ?thesis
        by (meson list.set_intros(1) uniqueAccum_in_lst)
    next
      case False
      then show ?thesis
      proof(cases "a = x")
        case True
        then show ?thesis 
          by (simp add: uniqueAccum_in_accum)
      next
        case False
        then show ?thesis
          apply simp
          try
          sorry
      qed
    qed
  qed
qed


lemma uniqueAccum_keeps_elements:
  shows "x \<in> set (uniqueAccum ys [])
      \<Longrightarrow> x \<in> set (uniqueAccum ys [a])"
proof(induction ys)
  case Nil
  then show ?case 
    by simp
next
  case (Cons y ys\<^sub>p)
  then show ?case 
    apply simp
  proof(cases "y = a")
    case True
    hence ya:"List.insert y [a] = [y]" 
      by simp
    hence "x \<in> set (uniqueAccum ys\<^sub>p [y])"
      using Cons.prems by auto
    then show "x \<in> set (uniqueAccum ys\<^sub>p (List.insert y [a]))"
      by (simp add: ya)
  next
    case False
    hence "List.insert y [a] = [y, a]" 
      by simp
    hence "uniqueAccum ys\<^sub>p (List.insert y [a]) = uniqueAccum ys\<^sub>p [y, a]"
      by simp
    (* have "set (uniqueAccum ys\<^sub>p [y, a]) = set ys\<^sub>p \<union> {y, a}" *)
    then show ?thesis sorry
  qed 

(*   proof(cases "x = y")
    case True
    then show ?thesis sorry
  next
    case False
    hence "x \<in> ys"
      sorry
    then show ?thesis sorry
  qed *)
qed
  oops

(*     assume "x \<in> set ys"
    then show "x \<in> set (uniqueAccum ys [y])" *)

(* https://isabelle.in.tum.de/community/FAQ#There_are_lots_of_arrows_in_Isabelle.2FHOL._What.27s_the_difference_between_-.3E.2C_.3D.3E.2C_--.3E.2C_and_.3D.3D.3E_.3F *)

lemma all_elements_present:
  fixes xs :: "nat list"
  assumes "x \<in> set xs"
  shows "x \<in> set xs \<Longrightarrow> x \<in> set (unique xs)"
proof(induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then show ?case 
    (* apply simp_all  *)
    apply auto
  proof -
    assume "x = y"
    then show "y \<in> set (uniqueAccum ys [y])"
      (* try *)
      sorry
  next
    assume "x \<in> set ys"
    then show "x \<in> set (uniqueAccum ys [y])"
      sorry
  qed
  oops
(*   proof(cases "x = y")
    case True

    then have "y \<in> set (uniqueAccum ys [y])"
      try
(*     then show ?thesis 
      apply simp_all *) 
      (* try *)
      sorry
  next
    case False
    then have "x \<in> set ys" 
      using Cons.prems by auto
    then show ?thesis 
      apply simp_all 
      (* try *)
      sorry
  qed
  oops *)

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