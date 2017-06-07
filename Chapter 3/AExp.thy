section "Arithmetic and Boolean Expressions"
  
theory AExp imports Main begin
  
subsection "Arithmetic Expressions"
  
type_synonym vname = string
type_synonym val = int
type_synonym state = "vname ⇒ val"
  
text_raw{*\snip{AExpaexpdef}{2}{1}{% *}
datatype aexp = N int | V vname | Plus aexp aexp
text_raw{*}%endsnip*}
  
text_raw{*\snip{AExpavaldef}{1}{2}{% *}
fun aval :: "aexp ⇒ state ⇒ val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a⇩1 a⇩2) s = aval a⇩1 s + aval a⇩2 s"
text_raw{*}%endsnip*}
  
  
value "aval (Plus (V ''x'') (N 5)) (λx. if x = ''x'' then 7 else 0)"
  
text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((λx. 0) (''x'':= 7))"
  
text {* A little syntax magic to write larger states compactly: *}
  
definition null_state ("<>") where
  "null_state ≡ λx. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"
  
text {* \noindent
  We can now write a series of updates to the function @{text "λx. 0"} compactly:
*}
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)
    
value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"
  
  
text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"
  
text{* Note that this @{text"<…>"} syntax works for any function space
@{text"τ⇩1 ⇒ τ⇩2"} where @{text "τ⇩2"} has a @{text 0}. *}
  
  
subsection "Constant Folding"
  
text{* Evaluate constant subsexpressions: *}
  
text_raw{*\snip{AExpasimpconstdef}{0}{2}{% *}
fun asimp_const :: "aexp ⇒ aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a⇩1 a⇩2) =
  (case (asimp_const a⇩1, asimp_const a⇩2) of
    (N n⇩1, N n⇩2) ⇒ N(n⇩1+n⇩2) |
    (b⇩1,b⇩2) ⇒ Plus b⇩1 b⇩2)"
text_raw{*}%endsnip*}
  
theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply (auto split: aexp.split)
  done
    
text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}
  
text_raw{*\snip{AExpplusdef}{0}{2}{% *}
fun plus :: "aexp ⇒ aexp ⇒ aexp" where
  "plus (N i⇩1) (N i⇩2) = N(i⇩1+i⇩2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a⇩1 a⇩2 = Plus a⇩1 a⇩2"
text_raw{*}%endsnip*}
  
lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  (* apply(induction a1 a2 rule: plus.induct) Original. The 'a1 a2' is extraneous. *)
  apply(induction rule: plus.induct)
    (* apply(induction a1) apply(induction a2)  Does not work*)
              apply simp_all (* just for a change from auto *)
  done
    
text_raw{*\snip{AExpasimpdef}{2}{0}{% *}
fun asimp :: "aexp ⇒ aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a⇩1 a⇩2) = plus (asimp a⇩1) (asimp a⇩2)"
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
    
    (* exercise 3.1 *)
 
fun is_N :: "aexp ⇒ bool" where
  "is_N (N _) = True"|
  "is_N _ = False"
  
  (* check that expression does not contain any unoptimized sub-expressions, 
      i.e. Plus (N i) (N j) *)
fun optimal :: "aexp ⇒ bool" where
  (* TODO why won't this, the ∧ function, work? *)
  (* "optimal (Plus e1 e2) = (is_N e1) ∧ (is_N e2)" | *)
  (* definition conj :: "[bool, bool] ⇒ bool"  (infixr "∧" 35) *)
  "optimal (Plus e1 e2) = Not(conj (is_N e1) (is_N e2))" |
  "optimal _ = True"
  
theorem asimp_const_is_optimal:
  "optimal (asimp_const e)"  
  apply(induction e)
    apply(auto)
  apply(simp split:aexp.split)
  done   
    
    (* Sum all N's found in expression. Change all values of (N x) to (N 0) in expression.
Assume that asimp will be run later to cleanup expressions like (Plus (N 0) (V v))
Because the only operator is '+' , we can blindly sum all N's.
helper for full_asimp *)
fun sum_Ns :: "aexp ⇒ int ⇒ (aexp × int)" where
  "sum_Ns (N n) s = (Plus (N 0) (N 0), s+n)"|
  "sum_Ns (V v) s = (V v, s)"|
  "sum_Ns (Plus e⇩1 e⇩2) s = 
    (let (re⇩1, s⇩1) = sum_Ns e⇩1 0;
         (re⇩2, s⇩2) = sum_Ns e⇩2 0
      in (Plus re⇩1 re⇩2, s⇩1 + s⇩2))"
 
(* When all variables are 0, aval = sum_Ns *)
lemma aval_sum_Ns:"aval e <> = snd (sum_Ns e 0)"
  apply(induction e)
    apply(auto)
   apply (simp add: null_state_def)
  by (simp add: case_prod_beta)
 
(* constant folding for aexp where we sum up all constants, even if they are not next to
each other. For example, Plus (N 1) (Plus (V x ) (N 2)) becomes Plus (V x ) (N 3). *)
fun full_asimp :: "aexp ⇒ aexp" where
   "full_asimp e⇩1 = (
      let (e⇩2, s) = sum_Ns e⇩1 0;
           e⇩3 = Plus (N s) e⇩2
      in  asimp e⇩3)"
   
value "full_asimp (Plus (N 1) (Plus (V x ) (N 2)))"
  
theorem aval_full_asimp[simp]:
  "aval (full_asimp e) s = aval e s"
  apply(induction e)
    apply(auto)
  by (simp add: case_prod_beta)
    (* by (simp add: case_prod_unfold) *)
    
(* Define a substitution function 
subst :: vname ⇒ aexp ⇒ aexp ⇒ aexp 
such that 
subst x a e 
is the result of replacing every
occurrence of variable x by a in e *)
fun subst :: "vname ⇒ aexp ⇒ aexp ⇒ aexp" where
  "subst matchMe replaceWith (V vname) = 
      (if matchMe = vname
      then replaceWith
      else V vname)"|
  "subst matchMe replaceWith (N n) = N n"|
  "subst matchMe replaceWith (Plus e⇩1 e⇩2) = 
      Plus (subst matchMe replaceWith e⇩1) (subst matchMe replaceWith e⇩2)"
  
value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')"
 
(*   Prove the so-called substitution lemma that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). As a consequence prove
aval a1 s = aval a2 s =⇒ aval (subst x a1 e) s = aval (subst x a2 e) s. *)
lemma substitution:"aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e) 
  by auto
    
theorem foo:
  "aval a⇩1 s = aval a⇩2 s 
  ⟹ aval (subst x a⇩1 e) s = aval (subst x a⇩2 e) s"
  apply(induction e)
  by auto
    
end
  
 
 
