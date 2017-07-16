theory Ex7_1 imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Small_Step" begin

section "Chapter 7 exercises"
  
subsection "7.1"
  
fun assigned :: "com \<Rightarrow> vname set" where
  "assigned (SKIP) = {}" |
  "assigned (Assign vname _) = {vname}" |
  "assigned (Seq  c0 c1) = assigned c0 \<union> assigned c1" |
  "assigned (If   _ c0 c1) = assigned c0 \<union> assigned c1" |
  "assigned (While  _ com) = assigned com"
  
lemma unassigned_is_unchanged:"\<lbrakk>(c,s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
  apply(induction rule: big_step_induct)
  by auto

subsection "7.2"

fun skip :: "com \<Rightarrow> bool" where
  "skip (SKIP) = True" |
  "skip (Assign _ _) = False" |
  "skip (Seq  c0 c1) = (skip c0 \<and> skip c1)" |
  "skip (If   _ c0 c1) = (skip c0 \<and> skip c1)" |
  (* I think we'd also need to know that While terminated, then this would be: = skip com *)
  "skip (While _ com) = False" 
  
lemma skip_like_SKIP: "skip c \<Longrightarrow> c \<sim> SKIP"
proof(induction c)
  case SKIP
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  then show ?case by fastforce
next
  case (If bexp c1 c2)
  then show ?case
    by (meson Big_Step.IfE big_step.IfFalse big_step.IfTrue skip.simps(4))
next
  case (While bexp c)
  then show ?case
    (* Note: this is how you view the simplifier steps *)
  using [[simp_trace_new mode=full]]
    by simp
qed

subsection "7.3"

fun deskip :: "com \<Rightarrow> com" where
  "deskip (SKIP) = SKIP" |
  "deskip (Assign v a)  = Assign v a" |
  "deskip (Seq  SKIP c) = c" |
  "deskip (Seq  c SKIP) = c" |
  "deskip (Seq  c0 c1)  = Seq c0 c1" |
  "deskip (If   b c0 c1) = If b c0 c1" |
  "deskip (While b c) = While b c" 

end
