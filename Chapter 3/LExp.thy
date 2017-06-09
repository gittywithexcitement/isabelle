section "Arithmetic and Boolean Expressions"
  
theory LExp imports Main begin
  
subsection "Arithmetic Expressions"
  
type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
  
text {* A little syntax magic to write larger states compactly: *}
  
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"
  
text {* \noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
lemma "<a := x, b := y> = (<> (a := x)) (b := (y::int))"
  by (rule refl)
    
lemma
  assumes "a \<noteq> b"
  shows"<a := x, b := y> = <b := (y::int), a := x>"
  using assms by auto
  
datatype aexp = N int | V vname | Plus aexp aexp
  
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"
 
    
text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"    
    
value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"  
  
  (* exercise 3.6 *)
  
(* The value of 
Let x e\<^sub>x\<^sub>_\<^sub>i\<^sub>s e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e
is: replace the value of x in the original state with e\<^sub>x\<^sub>_\<^sub>i\<^sub>s, and evaluate e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e using
the new state*)
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | Let vname lexp lexp
 
fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
  "lval (Nl n) s = n" |
  "lval (Vl x) s = s x" |
  "lval (Plusl a\<^sub>1 a\<^sub>2) s = lval a\<^sub>1 s + lval a\<^sub>2 s"|
  "lval (Let x e\<^sub>x\<^sub>_\<^sub>i\<^sub>s e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e) s\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r = lval e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e (s\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r(x := (lval e\<^sub>x\<^sub>_\<^sub>i\<^sub>s s\<^sub>o\<^sub>u\<^sub>t\<^sub>e\<^sub>r)))"
  
value "aval (Plus (V ''x'') (N 5)) <''x'' := 2>"
  
value "lval (Let ''x'' (Plusl (Nl 1)(Nl 3)) (Plusl (Vl ''x'') (Nl 5))) <''x'' := 2>"
  
(* Convert every lexp into the corresponding aexp.
Let will have to be converted into a (V x). *)  
fun inline :: "lexp \<Rightarrow> aexp"  where
  "inline (Nl n) = (N n)" |
 "inline (Vl x) = V x" |
 "inline (Plusl a\<^sub>1 a\<^sub>2) = Plus (inline a\<^sub>1) (inline a\<^sub>2)"|
(* Evaluate e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e, with the state that x := e\<^sub>x\<^sub>_\<^sub>i\<^sub>s *)
(* The expression Let x e\<^sub>x\<^sub>_\<^sub>i\<^sub>s e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e is inlined by substituting the converted form of e\<^sub>x\<^sub>_\<^sub>i\<^sub>s for x in the
converted form of e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e. *)
 (* I think the problem is that lval e\<^sub>x\<^sub>_\<^sub>i\<^sub>s uses the empty state *)
 "inline (Let x e\<^sub>x\<^sub>_\<^sub>i\<^sub>s e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e) = N (lval e\<^sub>e\<^sub>v\<^sub>a\<^sub>l\<^sub>_\<^sub>m\<^sub>e <x := (lval e\<^sub>x\<^sub>_\<^sub>i\<^sub>s <>)>)"
 
(* Prove the so-called substitution lemma that says that we can either substitute first and evaluate
afterwards or evaluate with an updated state *)
 (* lemma substitution:"aval (subst x a e) s = aval e (s(x := aval a s))" *)

theorem inline_substitution:
  (* The exercise didn't say to set s = <>, but there's no way the proof would work otherwise. I guess
it's possible I defined lval or inline incorrectly.*)
  shows "aval (inline expr) <> = lval expr <>"
  apply(induction expr arbitrary: s)
  by simp_all

    (* prove: *)
    (* lval expr2 <x1a := lval expr1 <>> = lval expr2 (s(x1a := lval expr1 s)) *)
    (* Evaluate expr1 using empty state; the variable referred to by x1a is now that N (a number).
    Evaluate expr2 with the state containing the one variable, x1a. *)
    (* Now compare the above to: *)
    (* Evaluate expr1 using state s; x1a is now that N. Evaluate expr2 using state s with x1a set as
    described. *)
    
    (* Obviously these are different, because s \<noteq> empty state. *)

    (* tried in vain *)
  (* apply(induction rule:inline.induct)  *)
  
subsection "Constant Folding"
  
text{* Evaluate constant subsexpressions: *}
  
fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)"
  
theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply (auto split: aexp.split)
  done
    
text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}
  
text_raw{*\snip{AExpplusdef}{0}{2}{% *}
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
text_raw{*}%endsnip*}
  
lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  (* apply(induction a1 a2 rule: plus.induct) Original. The 'a1 a2' is extraneous. *)
  apply(induction rule: plus.induct)
    (* apply(induction a1) apply(induction a2)  Does not work*)
              apply simp_all (* just for a change from auto *)
  done
    
text_raw{*\snip{AExpasimpdef}{2}{0}{% *}
fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"
text_raw{*}%endsnip*}
  
text{* Note that in @{const asimp_const} the optimized constructor was
inlined. Making it a separate function @{const plus} improves modularity of
the code and the proofs. *}
  
value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"
  
theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
  apply(induction a)
  apply simp_all
  done
    
(*     
(* Define a substitution function 
subst :: vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp 
such that 
subst x a e 
is the result of replacing every
occurrence of variable x by a in e *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst matchMe replaceWith (V vname) = 
      (if matchMe = vname
      then replaceWith
      else V vname)"|
  "subst matchMe replaceWith (N n) = N n"|
  "subst matchMe replaceWith (Plus e\<^sub>1 e\<^sub>2) = 
      Plus (subst matchMe replaceWith e\<^sub>1) (subst matchMe replaceWith e\<^sub>2)"
  
value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')"
 
(*   Prove the so-called substitution lemma that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). As a consequence prove
aval a1 s = aval a2 s =\<Rightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s. *)
lemma substitution:"aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e) 
  by auto
    
theorem foo:
  "aval a\<^sub>1 s = aval a\<^sub>2 s 
  \<Longrightarrow> aval (subst x a\<^sub>1 e) s = aval (subst x a\<^sub>2 e) s"
  apply(induction e)
  by auto *)
    
end
