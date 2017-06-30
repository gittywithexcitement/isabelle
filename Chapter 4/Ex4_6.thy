theory Ex4_6
  imports Main "~~/src/HOL/Library/Code_Target_Nat" "../Chapter 3/AExp"  
begin
  
section "Exercise 4.6"
  
inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  literal: "aval_rel (N x) s x" |  
  variable: "aval_rel (V name) state (state name)" |  
  plus: "aval_rel exp\<^sub>0 s value\<^sub>0 \<Longrightarrow> aval_rel exp\<^sub>1 s value\<^sub>1 
              \<Longrightarrow> aval_rel (Plus exp\<^sub>0 exp\<^sub>1) s (value\<^sub>0 + value\<^sub>1)"   
  
lemma "aval_rel (N 2) <> 2"
  using literal by simp
    
lemma "aval_rel (Plus (N 2) (N 4)) <> 6"
proof -
  have "aval_rel (N 2) <> 2" using literal by simp
  moreover have "aval_rel (N 4) <> 4" using literal by simp
  ultimately show "aval_rel (Plus (N 2) (N 4)) <> 6" using plus by fastforce
qed

end