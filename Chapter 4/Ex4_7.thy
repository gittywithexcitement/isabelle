theory Ex4_7
  imports Main "~~/src/HOL/Library/Code_Target_Nat" "../Chapter 3/ASMOrig"  
begin
  
section "Exercise 4.6"
  
inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "ok n [] n" |
  loadi: "ok n\<^sub>b is n\<^sub>a \<Longrightarrow> ok n\<^sub>b (is @ [LOADI _]) (n\<^sub>a + 1)" |
  load: "ok n\<^sub>b is n\<^sub>a \<Longrightarrow> ok n\<^sub>b (is @ [LOAD _]) (n\<^sub>a + 1)" |
  add: "ok n\<^sub>b is n\<^sub>a \<Longrightarrow> n\<^sub>a \<ge> 2 \<Longrightarrow> ok n\<^sub>b (is @ [ADD]) (n\<^sub>a - 1)"
  
theorem ok_computes_stack_size:
  "\<lbrakk>ok n instructions n'; length stack = n \<rbrakk> \<Longrightarrow> length (exec instructions state stack) = n'"
  apply(induction rule: ok.induct)
  by(simp_all)

lemma ok_append: "\<lbrakk>ok n\<^sub>a\<^sub>0 is1 n\<^sub>a; ok n\<^sub>b is0 n\<^sub>a\<^sub>0\<rbrakk> \<Longrightarrow> ok n\<^sub>b (is0 @ is1) n\<^sub>a"
  apply(induction (* arbitrary: n\<^sub>a Is bad here *) rule: ok.induct)
     apply simp
  using ok.loadi apply fastforce 
  using ok.load apply fastforce 
  using ok.add by fastforce 
    
theorem comp_cant_underflow: "ok n (comp expr) (n+1)"
  apply(induction expr arbitrary: n)
  using empty loadi apply fastforce 
  using empty load apply fastforce
  using add ok_append by fastforce

lemma ok_for_larger:"ok nb0 is na0 \<Longrightarrow> nb1 \<ge> nb0 \<Longrightarrow> ok nb1 is (na0 + (nb1 - nb0))"  
  apply(induction rule: ok.induct)
  using empty apply simp
  using loadi apply fastforce
  using load apply simp
  using add by fastforce
    
lemma test0_1:"ok 0 [LOADI 9] 1"
  using empty loadi by fastforce
    
lemma "ok 1 [LOADI 9] 2"
  using empty loadi 
  by (metis append_Nil nat_1_add_1)
    
lemma "ok n [LOADI 9] (n+1)"
  using empty loadi by fastforce
    
lemma test0_2:"ok 0 [LOADI 9, LOADI 9] 2"
  using test0_1 loadi
  by (metis Cons_eq_append_conv one_add_one)
    
lemma test1_3:"ok 1 [LOADI 9, LOADI 9] 3"
  using test0_2 ok_for_larger
  by (metis diff_diff_cancel diff_is_0_eq le_numeral_extra(4) nat_1_add_1 numeral_Bit1 numerals(1) zero_le_one) 
    
lemma "ok 2 [ADD] 1"
proof -
  have "ok 2 [] 2" 
    using empty by metis
  hence "ok 2 [ADD] (2-1)" using add by fastforce
  thus ?thesis by simp
qed
  
lemma add2_1:"ok 2 [ADD, LOADI 1] 2"
proof -
  have "ok 2 [] 2" 
    using empty by metis
  hence "ok 2 [ADD] 1" using add by fastforce
  hence "ok 2 [ADD, LOADI 1] (1+1)"
    using loadi
    by fastforce
  thus ?thesis
    by (metis one_add_one)
qed

end