theory Ex7_1 imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Small_Step" begin

section "Chapter 7 exercises"
  
fun assigned :: "com \<Rightarrow> vname set" where
  "assigned (SKIP) = {}" |
  "assigned (Assign vname _) = {vname}" |
  "assigned (Seq  c0 c1) = assigned c0 \<union> assigned c1" |
  "assigned (If   _ c0 c1) = assigned c0 \<union> assigned c1" |
  "assigned (While  _ com) = assigned com"
  
lemma unassigned_is_unchanged:"\<lbrakk>(c,s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
proof(induction c arbitrary: s t)
  case SKIP
  then show ?case by fastforce
next
  case (Assign x1 x2)
  then show ?case by fastforce
next
  case (Seq c1 c2)
  then show ?case 
    by (metis Big_Step.SeqE UnI1 UnI2 assigned.simps(3))
    (* by (metis SeqE Un_iff assigned.simps(3))  *)
next
  case (If x1 c1 c2)
  then show ?case by auto
next
  case (While bexp c)
  then show ?case 
  proof(cases "bval bexp s")
    case true:True      
        (* "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)" *)      
     apply_end simp
    have 0:"(\<And>s t. (c, s) \<Rightarrow> t \<Longrightarrow> s x = t x)"
      using While.IH While.prems(2) by auto
        (* have 1:"x \<notin> assigned c" 
      using While.prems(2) by auto *)
        (*         Need to manipulate
        (WHILE bexp DO c, s) \<Rightarrow> t
        into 
        (c, s) \<Rightarrow> t  *)
        (* I think I need to take a small step *)
    then have "(c, s) \<Rightarrow> t"
      using While.prems While.IH true 
      try0 sledgehammer
      sorry        
    then show ?thesis
      using While.prems While.IH true 
        (* using 0 *)
      try0 (* sledgehammer *)
      sorry        
  next
    case False
    then show ?thesis 
      using While.prems(1) by auto
  qed
qed
  
end
