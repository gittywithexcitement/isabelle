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
  
(* A tree is ordered if:
at a node, the value is > all values in the left child
and < all values in the right child 
and both of the node's children are ordered*)
  
fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node lc x rc) = (
    let gt_left = {y. y \<in> (to_set lc) \<and> (x \<le> y)} = {};
        lt_right = {y. y \<in> (to_set rc) \<and> (x \<ge> y)} = {}
    in gt_left \<and> lt_right \<and> ord lc \<and> ord rc)" 
  
value "ord (Node (Node Tip 2 Tip) 3 Tip)"
value "ord (Node Tip 0 (Node (Node Tip 1 Tip) 2 Tip))"
  
  
end