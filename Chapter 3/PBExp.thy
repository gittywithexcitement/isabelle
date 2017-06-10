theory PBExp imports AExp begin
  
subsection "Boolean Expressions"
  
datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp
 
type_synonym bstate = "vname \<Rightarrow> bool"
  
fun pbval :: "pbexp \<Rightarrow> bstate \<Rightarrow> bool" where
  "pbval (VAR x) s = s x" |
  "pbval (NOT b) s = (\<not> pbval b s)" |
  "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
  "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"
 
subsection "Exercise 3.9"
  
text{* Optimizing constructors: *}
  
 (* remove extraneous NOTs, i.e. NOT(NOT(x)) = x *)
fun notopt :: "pbexp \<Rightarrow> pbexp"where
  "notopt (VAR x) = (VAR x)" |
  "notopt (NOT b) = (
    case b of
      (NOT c) \<Rightarrow> notopt c|
      _       \<Rightarrow> NOT (notopt b))" |
 (* x       \<Rightarrow> NOT (notopt x))" | is more complex *)
  "notopt (AND b1 b2) = (AND (notopt b1) (notopt b2))" |
  "notopt (OR b1 b2) = (OR (notopt b1) (notopt b2))"
  
(* lemma not_preserves_value: "pbval exp s = pbval (notopt exp) s"
  
  
 1. \<And>exp s. (\<And>s. pbval exp s = pbval (notopt exp) s) \<Longrightarrow>
             (\<not> pbval (notopt exp) s) = pbval (case exp of NOT x \<Rightarrow> notopt x | _ \<Rightarrow> NOT (notopt exp)) s   *)
  
lemma not_preserves_value_v1[simp]: "pbval (notopt exp) s = pbval exp s"
proof(induction exp arbitrary: s)
  case (VAR x)
  then show ?case by simp
next
  case (NOT exp)
  show ?case 
  proof(induction exp arbitrary: s)
    case (VAR x)
    then show ?case by simp
  next
    case (NOT exp)
    then show ?case try0
  next
    case (AND exp1 exp2)
    then show ?case try0
  next
    case (OR exp1 exp2)
    then show ?case try0
  qed
    
    
    (* 1. \<And>exp s. 
      pbval (case exp of NOT x \<Rightarrow> notopt x | _ \<Rightarrow> NOT (notopt exp)) s 
      = (\<not> pbval exp s) *)
  have "pbval (notopt (NOT exp)) s = pbval (case exp of NOT x \<Rightarrow> notopt x | _ \<Rightarrow> NOT (notopt exp)) s"
    by simp
  have "pbval (NOT exp) s = (\<not> pbval exp s)" 
    by simp
      (* show "pbval (case exp of NOT x \<Rightarrow> notopt x | _ \<Rightarrow> NOT (notopt exp)) s = (\<not> pbval exp s)" sorry *)
      
      (* apply_end(simp_all) *)
      (* assume IH : "\<And>s. pbval (notopt exp_) s = pbval exp_ s" *)
      (* ?case \<equiv> pbval (notopt (NOT exp)) s = pbval (NOT exp) s *)
  (* show ?case *)
  proof cases
    (* case True *)
    assume "exp = NOT exp\<^sub>i\<^sub>n\<^sub>n\<^sub>e\<^sub>r"
    then show ?thesis try
  next
    case False
    then show ?thesis sorry
  qed
    
 
 (* then show ?case sorry *)
next
  case (AND exp1 exp2)
  then show ?case by simp
next
  case (OR exp1 exp2)
  then show ?case by simp
qed
 
  
lemma not_preserves_value_v2[simp]: "pbval (notopt exp) s = pbval exp s"
  (* apply(induction exp) *)
  apply(induction exp arbitrary: s) (* I don't think arbitrary:s makes a difference *)
     apply(simp_all)
    (* apply auto *) (* Leads to 2 unsolved goals *)
    (* apply(auto split: pbexp.split) *)
  (* apply(simp split: pbexp.split) *) (* I don't think this helps *)
    (* apply auto Will take us in circles*)
  (* apply(induction exp) Will take us in circles.*)
  (* nitpick sledgehammer *)
 
(* fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b" |
  "and b (Bc True) = b" |
  "and (Bc False) b = Bc False" |
  "and b (Bc False) = Bc False" |
  "and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"
 *)  
  
 
fun is_var::"pbexp \<Rightarrow> bool"  where
  "is_var (VAR _) = True"|
  "is_var _ = False"
  
  (* True when NOT is only applied to VARs. Otherwise, false.
What about not(not(var))? *)
fun is_nnf::"pbexp \<Rightarrow> bool"where
  "is_nnf (VAR x) = True" |
  "is_nnf (NOT b) = is_var b" |
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"
  
(* Converts a pbexp into NNF by pushing NOT inwards as much as possible. *)
fun nnf :: "pbexp \<Rightarrow> pbexp"where
  "nnf (VAR x) = True" |
  "nnf (NOT b) = is_var b" |
  "nnf (AND b1 b2) = (nnf b1 \<and> nnf b2)" |
  "nnf (OR b1 b2) = (nnf b1 \<and> nnf b2)"
 
 
  
(* text{* Optimizing constructors: *}
  
(* fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N n\<^sub>1) (N n\<^sub>2) = Bc(n\<^sub>1 < n\<^sub>2)" |
  "less a\<^sub>1 a\<^sub>2 = Less a\<^sub>1 a\<^sub>2"
 *)  
lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
  apply(induction a1 a2 rule: less.induct)
      apply simp_all
  done
    
text_raw{*\snip{BExpanddef}{2}{2}{% *}
fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b" |
  "and b (Bc True) = b" |
  "and (Bc False) b = Bc False" |
  "and b (Bc False) = Bc False" |
  "and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"
text_raw{*}%endsnip*}
  
lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
  apply(induction b1 b2 rule: and.induct)
                      apply simp_all
  done
    
text_raw{*\snip{BExpnotdef}{2}{2}{% *}
fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc True) = Bc False" |
  "not (Bc False) = Bc True" |
  "not b = Not b"
text_raw{*}%endsnip*}
  
lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
  apply(induction b rule: not.induct)
      apply simp_all
  done
    
text{* Now the overall optimizer: *}
  
text_raw{*\snip{BExpbsimpdef}{0}{2}{% *}
fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v) = Bc v" |
  "bsimp (Not b) = not(bsimp b)" |
  "bsimp (And b\<^sub>1 b\<^sub>2) = and (bsimp b\<^sub>1) (bsimp b\<^sub>2)" |
  "bsimp (Less a\<^sub>1 a\<^sub>2) = less (asimp a\<^sub>1) (asimp a\<^sub>2)"
text_raw{*}%endsnip*}
  
value "bsimp (And (Less (N 0) (N 1)) b)"
  
value "bsimp (And (Less (N 1) (N 0)) (Bc True))"
  
theorem "bval (bsimp b) s = bval b s"
  apply(induction b)
     apply simp_all
  done
    
    (* exercise 3.7 *)
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a\<^sub>l a\<^sub>r = And (Not (Less a\<^sub>l a\<^sub>r)) (Not (Less a\<^sub>r a\<^sub>l))"
  
value "bval (Eq (N 1) (N 1)) <>"
value "bval (Eq (N 1) (N 2)) <>"
 
fun LessEq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "LessEq a\<^sub>l a\<^sub>r = Not (Less a\<^sub>r a\<^sub>l)"
 
value "bval (LessEq (N 1) (N 1)) <>"
value "bval (LessEq (N 1) (N 2)) <>"
value "bval (LessEq (N 2) (N 1)) <>"
  
  (* exercise 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
  
fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
 "ifval (Bc2 v) s = v" |
 "ifval (If cond do_true do_false) s = (
    if (ifval cond s)
    then ifval do_true s
    else ifval do_false s)" |
 "ifval (Less2 a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"
 
fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "or bl br = Not (And (Not bl) (Not br))"
  
lemma or_commutative:"bval (or x y) = bval (or y x)"
  apply(induction x arbitrary: y)
  by auto
 
(* exclusive or *)
fun xor :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "xor bl br = And (Not (And bl br)) (or bl br)"
 
lemma xor_commutative:"bval (xor x y) = bval (xor y x)"
  apply(induction x arbitrary: y)
  by auto
 
fun if2bexp :: "ifexp \<Rightarrow> bexp" where
 "if2bexp (Bc2 v) = Bc v" |
 "if2bexp (If cond do_true do_false) = or (And (if2bexp cond) (if2bexp do_true)) (And (Not (if2bexp cond)) (if2bexp do_false))" |
 "if2bexp (Less2 a\<^sub>1 a\<^sub>2) = Less a\<^sub>1 a\<^sub>2"
 
fun b2ifexp::"bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bc2 v" |
  "b2ifexp (Not bexp) = (If (b2ifexp bexp) (Bc2 False) (Bc2 True))" |
  "b2ifexp (And b\<^sub>l b\<^sub>r) = (If (b2ifexp b\<^sub>l) (b2ifexp b\<^sub>r) (Bc2 False))" |
  "b2ifexp (Less a\<^sub>1 a\<^sub>2) = Less2 a\<^sub>1 a\<^sub>2"
  
lemma "bval (if2bexp ifexp) s = ifval ifexp s"  
  apply(induction ifexp)
  by auto
 *)
end
 
 
 
 
