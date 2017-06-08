section "Arithmetic and Boolean Expressions"
 
theory AMExp imports Main begin
 
subsection "Arithmetic Expressions"
 
type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
 
datatype expr = N int | V vname | Plus expr expr | Times expr expr
 
fun eval :: "expr \<Rightarrow> state \<Rightarrow> val" where
  "eval (N n) s = n" |
  "eval (V x) s = s x" |
  "eval (Plus a\<^sub>1 a\<^sub>2) s = eval a\<^sub>1 s + eval a\<^sub>2 s"|
  "eval (Times a\<^sub>1 a\<^sub>2) s = eval a\<^sub>1 s * eval a\<^sub>2 s"  
 
  value "eval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"
 
value "eval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"
 
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"
 
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)
 
value "eval (Plus (V ''x'') (N 5)) <''x'' := 7>"
 
value "eval (Plus (V ''x'') (N 5)) <''y'' := 7>"
 
subsection "Constant Folding"
 
fun plus :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
 
lemma eval_plus[simp]:
  "eval (plus a1 a2) s = eval a1 s + eval a2 s"
  (* apply(induction a1 a2 rule: plus.induct) Original. The 'a1 a2' is extraneous. *)
  apply(induction rule: plus.induct)
    (* apply(induction a1) apply(induction a2)  Does not work*)
              apply simp_all (* just for a change from auto *)
  done
    
fun times :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "times (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1 * i\<^sub>2)" |
  "times (N i) a = (if i=0 
                    then (N 0) 
                    else (if i=1 
                      then a
                      else Times (N i) a))" |
  "times a (N i) = (if i=0 
                    then (N 0) 
                    else (if i=1 
                      then a
                      else Times a (N i)))" |
  "times a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"
  
lemma eval_times[simp]:
  "eval (times a1 a2) s = eval a1 s * eval a2 s"
  (* apply(induction a1 a2 rule: times.induct) Original. The 'a1 a2' is extraneous. *)
  apply(induction rule: times.induct)
    apply simp_all
  done  
  
fun asimp :: "expr \<Rightarrow> expr" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
  "asimp (Times a\<^sub>1 a\<^sub>2) = times (asimp a\<^sub>1) (asimp a\<^sub>2)"
 
value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"
 
theorem eval_asimp[simp]:
  "eval (asimp a) s = eval a s"
  apply(induction a)
  apply simp_all
  done
 
(* Define a substitution function
subst :: vname \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr
such that
subst x a e
is the result of replacing every
occurrence of variable x by a in e *)
fun subst :: "vname \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
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
eval (subst x a e) s = eval e (s(x := eval a s)). As a consequence prove
eval a1 s = eval a2 s =\<Rightarrow> eval (subst x a1 e) s = eval (subst x a2 e) s. *)
lemma substitution:"eval (subst x a e) s = eval e (s(x := eval a s))"
  apply(induction e)
  by auto
 
theorem foo:
  "eval a\<^sub>1 s = eval a\<^sub>2 s
  \<Longrightarrow> eval (subst x a\<^sub>1 e) s = eval (subst x a\<^sub>2 e) s"
  apply(induction e)
  by auto
 
end
  