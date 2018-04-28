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
      try
      sorry
  next
    assume "x \<in> set ys"
    then show "x \<in> set (uniqueAccum ys [y])"
      sorry
  qed
qed
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
(* qed *)

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