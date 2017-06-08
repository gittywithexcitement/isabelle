theory 10
  imports Main "~~/src/HOL/Library/Code_Target_Nat" 
begin
  
  (* section 2.5 *)
  
  (* I don't understand this:
In particular, let-expressions can be unfolded by making Let_def a simplification
rule *)
  
  (* exercise 2.10 *) 
datatype tree0 = Leaf | Node tree0 tree0
  
fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Leaf = Suc 0"|
  "nodes (Node l r) = Suc(nodes l + nodes r)"
  
value "nodes Leaf"
value "nodes (Node Leaf Leaf)"
  
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"
  
value "nodes (explode 1 (Node Leaf Leaf))" (* x*2+1 where x=3, is 7 *)
value "nodes (explode 2 (Node Leaf Leaf))" (* do it twice where x=3, is 15 *)
  
value "nodes (explode 1 (Leaf))" (* x*2+1 where x=1, is 3 *)
value "nodes (explode 2 (Leaf))" (* do it twice where x=1, is 7 *)
  
value "nodes (explode 1 (Node Leaf (Node Leaf Leaf)))" (* go once where x=5, is 11 *)  
value "nodes (explode 2 (Node Leaf (Node Leaf Leaf)))" (* go twice where x=5, is 23 *)  
  
value "x*2+1 :: int"  
value "(x*2+1)*2+1 :: int"
  
  (* Find an equation expressing the size of a tree after exploding it (nodes
(explode n t)) as a function of nodes t and n. Prove your equation   *)
lemma nodes_explode[simp]: "nodes (explode n t) = (2^n) * (nodes t) + (2^n - 1)"
  
  (* apply(induction n) *)
  (* After simp_all, this goal remains:
 1. \<And>n. nodes (explode n t) = 2 ^ n + nodes t * 2 ^ n - Suc 0 \<Longrightarrow>
         nodes (explode n (Node t t)) = 2 * 2 ^ n + nodes t * (2 * 2 ^ n) - Suc 0 *)
  
  apply(induction n arbitrary: t)
   apply(simp_all add: algebra_simps)
  done
     
end