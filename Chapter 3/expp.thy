section "Arithmetic and Boolean Expressions"
 
theory expp (* short for for expression ++ *)
  imports Main "~~/src/HOL/Library/Code_Target_Nat" 
begin
  
  (* exercise 3.5
impl post-increment
division operation *)

subsection "State"  
 
type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
  
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"
 
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

subsection "Arithmetic Expressions"
 
datatype expr = N int | V vname | PostIncr vname | Plus expr expr | Times expr expr | Div expr expr
  
(* Returns the updated state *)
fun increment_variable :: "vname \<Rightarrow> state \<Rightarrow> state" where
  "increment_variable v s = 
    (let before = s v
        in s (v := before + 1))"
 
fun eval :: "expr \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "eval (N n) s = Some (n, s)" |
  "eval (V v) s = Some (s v, s)" |
  "eval (PostIncr v) s = Some (s v, increment_variable v s)" |
  "eval (Plus a\<^sub>1 a\<^sub>2) s = 
    (case eval a\<^sub>1 s of
      None \<Rightarrow> None
    | Some (r\<^sub>1, s\<^sub>1) \<Rightarrow> 
      (case eval a\<^sub>2 s\<^sub>1 of
        None \<Rightarrow> None
      | Some (r\<^sub>2, s\<^sub>2) \<Rightarrow> Some (r\<^sub>1 + r\<^sub>2, s\<^sub>2)))"|
  "eval (Times a\<^sub>1 a\<^sub>2) s = 
    (case eval a\<^sub>1 s of
      None \<Rightarrow> None
    | Some (r\<^sub>1, s\<^sub>1) \<Rightarrow> 
      (case eval a\<^sub>2 s\<^sub>1 of
        None \<Rightarrow> None
      | Some (r\<^sub>2, s\<^sub>2) \<Rightarrow> Some (r\<^sub>1 * r\<^sub>2, s\<^sub>2)))"|
  "eval (Div a\<^sub>1 a\<^sub>2) s = 
    (case eval a\<^sub>1 s of
      None \<Rightarrow> None
    | Some (r\<^sub>1, s\<^sub>1) \<Rightarrow> 
      (case eval a\<^sub>2 s\<^sub>1 of
        None \<Rightarrow> None
      | Some (r\<^sub>2, s\<^sub>2) \<Rightarrow> 
        (if r\<^sub>2 = 0
          then None
          else Some (r\<^sub>1 div r\<^sub>2, s\<^sub>2))))"
  
value "eval (Div (N 8) (N 2)) <>"
value "eval (Div (N 8) (N 0)) <>"
  
value "eval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"
 
value "eval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"
 
value "eval (Plus (V ''x'') (N 5)) <''x'' := 7>"
 
value "eval (Plus (V ''x'') (N 5)) <''y'' := 7>"
  
value "eval (Plus (V ''x'') (V ''x'')) <''x'' := 1>"

  (* test post increment *)
value "eval (Plus (PostIncr ''x'') (PostIncr ''x'')) <''x'' := 1>"

subsection "Constant Folding"
 
fun plus :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
     
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

fun asimp :: "expr \<Rightarrow> expr" where
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
  "asimp (Times a\<^sub>1 a\<^sub>2) = times (asimp a\<^sub>1) (asimp a\<^sub>2)"|
  (* Don't recurse inside N, V, or PostIncr *)
  "asimp e = e"
 
value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

end
  