theory Ex4_7
  imports Main "~~/src/HOL/Library/Code_Target_Nat" "../Chapter 3/ASM"  
begin
  
section "Exercise 4.6"
  
inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "ok n [] n" |
  loadi: "ok _ is n \<Longrightarrow> ok _ ((LOADI _) # is) (n + 1)" |
  (* literal: "ok nb is na \<Longrightarrow> ok n ((LOADI _) # is) (na + 1)" *)
  load: "ok _ is n \<Longrightarrow> ok _ ((LOAD _) # is) (n + 1)" |
  add: "ok _ is n \<Longrightarrow> n \<ge> 2 \<Longrightarrow> ok _ (ADD # is) (n - 2)"
  (* add: "ok _ is _ \<Longrightarrow> n \<ge> 2 \<Longrightarrow> ok n (ADD # is) (n - 2)" *)
  
  (* datatype instr = LOADI val | LOAD vname | ADD *)
  
lemma test0_1:"ok 0 [LOADI 9] 1"
  using empty loadi by fastforce
    
lemma "ok 1 [LOADI 9] 2"
  using empty loadi by (metis nat_1_add_1)
    
lemma "ok n [LOADI 9] (n+1)"
  using empty loadi by blast 
    
lemma test0_2:"ok 0 [LOADI 9, LOADI 9] 2"
  using test0_1 loadi by (metis one_add_one)
  
lemma test1_3:"ok 1 [LOADI 9, LOADI 9] 3"
  using loadi 
  by (metis add.commute add_One add_One_commute empty inc.simps(2) nat_1_add_1 one_plus_numeral)    

end