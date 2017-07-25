theory Scratch
  imports Main
begin
  
datatype mybool = MTrue | MFalse
  
fun myconj :: "mybool \<Rightarrow> mybool \<Rightarrow> mybool" where
  "myconj MTrue MTrue = MTrue" |
  "myconj _    _    = MFalse"
  
value "myconj MTrue MFalse"
  
datatype mynat = MZero | MSuc mynat
  
fun myadd :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
  "myadd MZero    r = r" |
  "myadd (MSuc l) r = MSuc(myadd l r)"
  (* "myadd (MSuc l) r = myadd l (MSuc r)" *)
  
lemma add_02: "myadd l MZero = l"
  apply(induction l)
   apply(auto)
  done
    
value "myadd (MSuc MZero) MZero"
  
datatype 'a list = Nil | Cons 'a "'a list"
  
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"
  
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" |
  "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
  
  
value "rev(Cons True (Cons False Nil))"
value "rev(Cons a (Cons b Nil))"
  
end