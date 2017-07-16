theory Ex7_1 imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Small_Step" begin

section "Chapter 7 exercises"
  
fun assigned :: "com \<Rightarrow> vname set" where
  "assigned (SKIP) = {}" |
  "assigned (Assign vname _) = {vname}" |
  "assigned (Seq  c0 c1) = assigned c0 \<union> assigned c1" |
  "assigned (If   _ c0 c1) = assigned c0 \<union> assigned c1" |
  "assigned (While  _ com) = assigned com"
  
lemma unassigned_is_unchanged:"\<lbrakk>(c,s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
  apply(induction rule: big_step_induct)
  by auto
  
end
