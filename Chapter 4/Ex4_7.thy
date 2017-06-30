theory Ex4_7
  imports Main "~~/src/HOL/Library/Code_Target_Nat" "../Chapter 3/ASM"  
begin
  
section "Exercise 4.6"
  
inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "ok n [] n" |
  loadi: "ok _ is n \<Longrightarrow> ok _ ((LOADI _) # is) (n + 1)" |
  load: "ok _ is n \<Longrightarrow> ok _ ((LOAD _) # is) (n + 1)" |
  add: "ok _ is n \<Longrightarrow> n\<^sub>a\<^sub>t\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t \<ge> 2 \<Longrightarrow> ok n\<^sub>a\<^sub>t\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t (ADD # is) (n - 2)"

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

    (* TODO test add *)
    
end