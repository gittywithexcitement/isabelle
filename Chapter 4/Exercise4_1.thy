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
    
end