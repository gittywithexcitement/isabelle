theory Ex4_7
  imports Main "~~/src/HOL/Library/Code_Target_Nat" "../Chapter 3/ASM"  
begin
  
section "Exercise 4.6"
  
inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "ok n [] n" |
  loadi: "ok _ is _ \<Longrightarrow> ok n ((LOADI _) # is) (n + 1)" |
  (* literal: "ok nb is na \<Longrightarrow> ok n ((LOADI _) # is) (na + 1)" *)
  load: "ok _ is _ \<Longrightarrow> ok n ((LOAD _) # is) (n + 1)" |
  add: "ok _ is _ \<Longrightarrow> n \<ge> 2 \<Longrightarrow> ok n (ADD # is) (n - 2)"
  
  (* datatype instr = LOADI val | LOAD vname | ADD *)
  
lemma test0:"ok 0 [LOADI 9] 1"
  using empty loadi by fastforce

lemma "ok 1 [LOADI 9] 2"
  using empty loadi by (metis nat_1_add_1)

lemma test1:"ok 0 [LOADI 9, LOADI 9] 2"
  using loadi test0   sledgehammer
(* proof -
  have "ok 0 [LOADI 9] 1" using test0 by simp
  then have "ok 0 [LOADI 9, LOADI 9] 2"
 *)    

(* lemma "aval_rel (Plus (N 2) (N 4)) <> 6"
proof -
  have "aval_rel (N 2) <> 2" using literal by simp
  moreover have "aval_rel (N 4) <> 4" using literal by simp
  ultimately show "aval_rel (Plus (N 2) (N 4)) <> 6" using plus by fastforce
qed
 *)  
  
  
end