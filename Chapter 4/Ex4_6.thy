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
  
lemma aval_rel_implies_aval:"aval_rel exp state v \<Longrightarrow> aval exp state = v"
  apply(induction rule: aval_rel.induct)
  by simp_all
    
lemma aval_implies_aval_rel:"aval exp state = v \<Longrightarrow> aval_rel exp state v"
  (* This is a great example of 'arbitrary' being required.
If you do induction without arbitrary v, then the third case, plus, can't be solved. The inductive
hypotheses are too weak; if you used them you would essentially be saying: (v + v = v)
The two premises of the induction hypothesis each say that the evaluation of their own
expression equals some v; we need 'arbitrary' to indicate that these v may be different from each
other, and different from the v in the proposition we are proving.
This is what the goal looks like without aribtrary:

 3. \<And>exp1 exp2.
       (aval exp1 state = v \<Longrightarrow> Ex4_6.aval_rel exp1 state v) \<Longrightarrow>
       (aval exp2 state = v \<Longrightarrow> Ex4_6.aval_rel exp2 state v) \<Longrightarrow> 
        aval (Plus exp1 exp2) state = v 
    \<Longrightarrow> Ex4_6.aval_rel (Plus exp1 exp2) state v

Obviously, the 'v' in the first two lines should be different from the v in the last line, hence
'arbitrary' is required. *)
  apply(induction exp arbitrary: v)
    apply (simp add: literal)
  using variable apply auto[1]
  using plus by auto
    
lemma "aval exp state = v \<longleftrightarrow> aval_rel exp state v"
  apply rule
   apply (simp add: aval_implies_aval_rel)
  by (simp add: aval_rel_implies_aval)
    
    
end