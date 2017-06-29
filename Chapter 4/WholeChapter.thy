theory WholeChapter
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
  
section "Exercises from Software Foundations, Inductively Defined Propositions"
  
lemma n_doubled_is_even:"ev (n * 2)"
  apply(induction n)
   apply (simp add: ev0)
  by (simp add: evSS)
    
lemma "ev (Suc (Suc n)) \<Longrightarrow> ev n"
  using ev.simps by blast
    
lemma even_implies_doubled:"ev n \<Longrightarrow> \<exists>k. n = (k * 2)"
  apply(induction rule: ev.induct)
   apply simp
  by arith

lemma even_equivalent_doubled: "ev n \<longleftrightarrow> (\<exists>k. n = (k * 2))"
  apply(rule)
   apply(simp add:even_implies_doubled)
  using n_doubled_is_even by auto
    
lemma "ev n \<Longrightarrow> ev m \<Longrightarrow> ev (n + m)"
  apply(induction rule: ev.induct)
   apply simp
  apply(simp)
  by (simp add: evSS)
    
lemma ev_n_ev_m_plus:"ev n \<Longrightarrow> ev m \<Longrightarrow> ev (n+m)"
  apply(induction rule:ev.induct)
   apply simp
  apply(simp)
  by (simp add: evSS)
    
inductive ev' :: "nat \<Rightarrow> bool" where
  ev'0: "ev' 0" |
  ev'2: "ev' 2" |
  ev'sum: "ev' n \<Longrightarrow> ev' m \<Longrightarrow> ev' (n+m)"
  
lemma ev_equivalent_ev':"ev n \<longleftrightarrow> ev' n"
  apply(rule)
   apply(induction rule:ev.induct)
    apply (simp add: ev'0)
  using ev'2 ev'sum apply force
  apply(induction rule:ev'.induct)
    apply (simp add: ev0)
   apply (simp add: ev0 evSS numeral_2_eq_2)
  using ev_n_ev_m_plus by simp
    
    (* if stuck, flip order of premises *)
lemma ev_n_plus_m:"ev (n+m) \<Longrightarrow> ev n \<Longrightarrow> ev m"
  apply(induction rule:ev.induct)
   apply(simp_all)
  oops
    
lemma ev_n_plus_m:"ev n \<Longrightarrow> ev (n+m) \<Longrightarrow> ev m"
  apply(induction rule:ev.induct)
   apply(simp_all)
  using ev.simps by blast
    
section "Exercises from Software Foundations, inductive relations"

inductive le :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  eq: "le x x" |
  grow: "le x y \<Longrightarrow> le x (Suc y)"
  
  (* test: inductive le *)
lemma "le 2 2"
  by (metis eq)
lemma "le 1 2"
  by (metis Suc_1 eq grow)

definition lt :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lt x y = le (Suc x) y" 

lemma "lt 1 2"
  by (simp add: eq lt_def numeral_2_eq_2)
        
section "End exercises from Software Foundations"      
  
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
  apply(induction rule: evn.induct)
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
  
lemma star_transitive: "star r a b \<Longrightarrow> star r b c \<Longrightarrow> star r a c"
  apply(induction rule: star.induct)
   apply(assumption)
  apply(simp)
    (* by(metis step) *)
  by(metis star.step)
    
subsection "Exercise 4.2"
  
inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty: "palindrome []"|
  singleton: "palindrome [x]"|
  step: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"
  
lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  by(simp_all)
    
subsection "exercise 4.3"
  
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"
  
(* This version is hard (impossible?) to prove   *)
lemma starp_transitive:"star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(simp)
  oops
    
(* By flipping the assumption order so that rule induction is applied to (star' r y z), this is easy
to prove *)
lemma starp_transitive:"star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(simp)
  apply(simp)
  by (metis star'.step')
    
lemma starp_implies_star:"star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(metis star.refl)
  by(metis star.refl star.step star_transitive)
    
lemma star_implies_starp:"star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(metis star'.refl')
  by (metis refl' starp_transitive step')

subsection "exercise 4.4"    
    
    
end