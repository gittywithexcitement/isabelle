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
  "skip (While  _ com) = skip com"
  
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
    proof(cases "bval bexp s")
      case True
      then show ?thesis     try0 sorry
    next
      case False
      then show ?thesis     try0 sorry
    qed
next
  case (While x1 c)
  then show ?case try0 sorry
qed
  
end
