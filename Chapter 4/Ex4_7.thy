theory Ex4_7
  imports Main "~~/src/HOL/Library/Code_Target_Nat" "../Chapter 3/ASMOrig"  
begin
  
section "Exercise 4.6"
  
inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "ok n [] n" |
  loadi: "ok n\<^sub>b is n\<^sub>a \<Longrightarrow> ok n\<^sub>b ((LOADI _) # is) (n\<^sub>a + 1)" |
  load: "ok n\<^sub>b is n\<^sub>a \<Longrightarrow> ok n\<^sub>b ((LOAD _) # is) (n\<^sub>a + 1)" |
  add: "ok n\<^sub>b is n\<^sub>a \<Longrightarrow> n\<^sub>b \<ge> 2 \<Longrightarrow> ok n\<^sub>b (ADD # is) (n\<^sub>a - 1)"
  
theorem ok_computes_stack_size:
  "\<lbrakk>ok n instructions n'; length stack = n \<rbrakk> \<Longrightarrow> length (exec instructions state stack) = n'"
proof(induction rule: ok.induct) (* arbitrary n? stack?*)
  case (empty n)
  then show ?case by simp
next
  case (loadi n\<^sub>b instrs n\<^sub>a val)
    apply_end(rename_tac n\<^sub>b instrs n\<^sub>a val)

  have "exec (LOADI val # instrs) state stack = exec instrs state (exec1 (LOADI val) state stack)"
    by simp
  also have "... = exec instrs state (val # stack)" by simp

  then show ?case try0 sledgehammer sorry
next
  case (load n\<^sub>b "is" n\<^sub>a uv)
  then show ?case (* try0 sledgehammer *) sorry
next
  case (add n\<^sub>b "is" n\<^sub>a)
  then show ?case (* try0 sledgehammer *) sorry
qed 
  
(*case (empty  n)
  then show ?case 
    by simp
next
  (* case (loadi lenStk instrs lenInstrsRslt l val) *)
 case (loadi uu "is" n uv uw)
   apply_end(rename_tac lenStk instrs lenInstrsRslt l val)
    (* case_names rename_tac len0 instrctns len1 uv uw *)
  have "exec (LOADI val # instrs) state stack = exec instrs state (exec1 (LOADI val) state stack)"
    by simp
    (* n # stk *)
  also have "... = exec instrs state (val # stack)" by simp
    
    
    (*     fix len0 instrs len1 lngthstck val
    let "?case" = "length (exec (LOADI val # instrs) state stack) = len1 + 1"
    assume hyps : "ok len0 instrs len1" 
      and IH : "length stack = len0 \<Longrightarrow> length (exec instrs state stack) = len1" 
      and prems : "length stack = lngthstck" *)
    
    (* apply_end(simp) *)
  then show ?case sledgehammer sorry
next
  case (load ux instructions n uy uz)
  then show ?case (* sledgehammer *) sorry
next
  case (add va instructions n n\<^sub>a\<^sub>t\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t)
  then show ?case (* sledgehammer *) sorry
qed  *)
    
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
    
lemma "ok 2 [ADD] 1"
proof -
  have "ok 2 [] 2" 
    using empty by metis
  hence "ok 2 [ADD] (2-1)" using add by blast
  thus ?thesis by simp
qed
  
lemma add2_1:"ok 2 [ADD, LOADI 1] 2"
proof -
  have "ok 2 [] 2" 
    using empty by metis
  hence "ok 2 [ADD] 1" using add by fastforce
  hence "ok 2 [ADD, LOADI 1] (1+1)"
    using loadi 
    by (metis \<open>ok 2 [] 2\<close> add add_diff_cancel_left' dual_order.refl nat_1_add_1 one_plus_numeral_commute)
  thus ?thesis
    by (metis one_add_one)
qed
  
end