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
(* "insert x xs = (if x \<in> set xs then xs else x # xs)" *)

fun unique :: "nat list => nat list" where
  "unique xs = uniqueAccum xs []"

fun listElem :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "listElem [] a = False" |
  "listElem (x # xs) a = (if x = a then True else listElem xs a)"

fun tails :: "'a list \<Rightarrow> 'a list list" where
  "tails [] = []" |
  "tails (x # xs) = (x # xs) # (tails xs)"

(* Prove: 

All elements of the original list are in the output

Every element of the output is distinct

Note from webpage author:

I specified that all elements of the original list are in the output, but not
that all elements of the output were in the original list. If the method took
in [1, 2, 2] and returned [1, 2, 99], it would still pass the partial
specification. I really dropped the ball on this one. *)

section \<open>Proofs\<close>

subsection \<open>Helper lemmas\<close>

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
  by simp

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

subsection \<open>All elements of the original list are elements of the output\<close>

lemma all_elements_present:
  shows "x \<in> set xs \<Longrightarrow> x \<in> set (unique xs)"
  by (simp add: uniqueAccum_in_lst)

subsection \<open>Every element of the output is distinct\<close>

lemma output_elements_distinct:
  shows "card (set (unique xs)) = length (unique xs)"
proof(induction xs)
  case Nil
  then show ?case 
    by simp
next
case (Cons x xs)
  then show ?case 
    apply auto
  proof -
    show "card (set (uniqueAccum xs [x])) = length (uniqueAccum xs [x])" 
    proof(cases "x \<in> set xs")
      case x_in_xs:True
      hence "card (set (uniqueAccum xs [x])) = card (set (uniqueAccum xs []))"
        by (metis Un_insert_right card_set list.set(1) list.set(2) remdups.simps(2) sup_bot.comm_neutral uniqueAccum_set_union)
      have "set (uniqueAccum xs [x]) = set (uniqueAccum xs [])"
        using x_in_xs uniqueAccum_set_union by auto
      hence "length (uniqueAccum xs [x]) = length (uniqueAccum xs [])" 
        try
        sorry
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
(* qed *)oops

lemma output_elements_distinct:
  shows "distinct (unique xs)"
proof(induction xs)
  case Nil
  then show ?case 
    by simp
next
case (Cons x xs\<^sub>p)
  then show ?case 
    apply auto
  proof(cases "x \<in> set xs\<^sub>p")
    case True
      (* "distinct (x # xs) \<longleftrightarrow> x \<notin> set xs \<and> distinct xs" *)
    (* hence "set (uniqueAccum xs\<^sub>p []) = set (uniqueAccum xs\<^sub>p [x])"
      using uniqueAccum_set_union by auto *)
        
    (* We know: distinct (unique xs\<^sub>p) *)

    then show "distinct (uniqueAccum xs\<^sub>p []) \<Longrightarrow> distinct (uniqueAccum xs\<^sub>p [x])" 
      (* try *)
      sorry
  next
    case False
    then show "distinct (uniqueAccum xs\<^sub>p []) \<Longrightarrow> distinct (uniqueAccum xs\<^sub>p [x])" sorry
  qed
qed
