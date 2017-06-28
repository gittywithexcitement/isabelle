(* exercise 3.12 *)
theory Exercise4_1
  imports Main "~~/src/HOL/Library/Code_Target_Nat"  
begin
  
section "Exercise 4.1"
  
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
  
fun to_set :: "'a tree \<Rightarrow> 'a set" where
  "to_set Tip = {}" |
  "to_set (Node lc x rc) = {x} \<union> to_set lc \<union> to_set rc"
  
value "to_set Tip"
value "to_set (Node Tip 0 (Node (Node Tip 2 Tip) 1 Tip)) :: int set"
  
  (* A tree is ordered iff:
at a node, the value is > all values in the left child
and < all values in the right child 
and both of the node's children are ordered*)  
fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node lc x rc) = (
    let gt_left = (\<forall>y \<in> (to_set lc). x > y);
        lt_right = (\<forall>y \<in> (to_set rc). x < y)
    in gt_left \<and> lt_right \<and> ord lc \<and> ord rc)" 
  
value "ord (Node (Node Tip 2 Tip) 3 Tip)"
value "ord (Node Tip 0 (Node (Node Tip 1 Tip) 2 Tip))"
  
  (* Insert element into ordered int tree, preserving order   *)
fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins x Tip = Node Tip x Tip" |  
  "ins x (Node lc tx rc) = (
    if x < tx
    then Node (ins x lc) tx rc
    else (
      if x > tx
      then Node lc tx (ins x rc)
      else (Node lc tx rc)))"  
  
value "ins 1 (Node (Node Tip 2 Tip) 4 Tip)"
value "ins 2 (Node (Node Tip 2 Tip) 4 Tip)"
value "ins 3 (Node (Node Tip 2 Tip) 4 Tip)"
value "ins 5 (Node (Node Tip 2 Tip) 4 Tip)"
  
value "ord (ins 1 (Node (Node Tip 2 Tip) 4 Tip))"
value "ord (ins 2 (Node (Node Tip 2 Tip) 4 Tip))"
value "ord (ins 3 (Node (Node Tip 2 Tip) 4 Tip))"
value "ord (ins 5 (Node (Node Tip 2 Tip) 4 Tip))"
  
theorem ins_tree_like_insert_set:"to_set (ins x tree) = {x} \<union> to_set tree"
  apply(induction tree)
  by auto
    
theorem ins_preserves_order: "ord tree \<Longrightarrow> ord (ins x tree)"
  (* I thought arbitrary x would be needed. It's not. *)
  apply(induction tree)
   apply(simp)
  apply(simp) 
  using ins_tree_like_insert_set by simp
    
lemma "\<lbrakk> (a::nat)\<le>b; b\<le>c; c\<le>d; d\<le>e \<rbrakk> \<Longrightarrow> a\<le>e"
  (* by linarith *)
  by (blast intro:le_trans)
    
lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (blast dest: Suc_leD)
    
inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"
  
fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"|  
  "evn (Suc 0) = False"|  
  "evn (Suc(Suc n)) = evn n"  
  
lemma "ev(Suc(Suc(Suc(Suc 0))))"
  apply(rule evSS)
  apply(rule evSS)
  apply(rule ev0)
  done
    
lemma ev_to_evn:"ev m \<Longrightarrow> evn m"
  (*   apply(induction m) 
    Bad because it creates this goal:
    2. \<And>m. (ev m \<Longrightarrow> evn m) \<Longrightarrow> ev (Suc m) \<Longrightarrow> evn (Suc m) *)
  apply(induction rule: ev.induct)
  by simp_all
    
lemma evn_to_ev:"evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
  by(simp_all add: ev0 evSS)
    
lemma "evn n = ev n"
  (*   find_theorems intro
using [[rule_trace]] apply(rule HOL.iffI) *)
  apply(rule)
   apply(metis evn_to_ev)
  apply(metis ev_to_evn)
  done
    
declare ev.intros[simp,intro]
  
  (* The “for r” in the header is merely a hint to Isabelle that r is a fixed parameter of star, in
contrast to the further parameters of star, which change. As a result, Isabelle generates a simpler
induction rule *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  
lemma star_transitive: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(assumption)
  apply(simp)
    (* by(metis step) *)
  by(metis star.step)
    
section "Exercise 4.2"
  
inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty: "palindrome []"|
  singleton: "palindrome [x]"|
  step: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"
  
lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  by(simp_all)
    
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"
  
lemma starp_transitive:"star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  (* apply(induction arbitrary: z rule: star'.induct) *)
  apply(induction rule: star'.induct)
   apply(simp)
  apply(rule)
   apply(simp)
    (* sledgehammer *)
    (* apply(simp) *)
    using star'.step' star'.refl'  (* try0 *)  (* sledgehammer *) 
    (* apply(simp add: star'.step') *)
    (* star' r x y \<Longrightarrow> (star' r y z \<Longrightarrow> star' r x z) \<Longrightarrow> r y za \<Longrightarrow> star' r za z \<Longrightarrow> star' r x z *)
    oops
  
lemma starp_implies_star:"star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(metis star.refl)
  by(metis star.refl star.step star_transitive)

lemma star_implies_starp:"star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(metis star'.refl')
    sledgehammer
  (* by(metis star.refl star.step star_transitive) *)

end