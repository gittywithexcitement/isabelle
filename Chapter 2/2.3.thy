theory 3
  imports Main
begin
  
  (* exercise 2.3 *) 
  
  (* this exercise can't appear in the same file as 2.2, because the nat type used in count would
  then be different than the nat type used by the library-defined length *)
  
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where 
  "count v Nil = 0" 
| "count v (Cons x xs) = (if v=x then Suc (count v xs) else count v xs)"
  
value "count (1::int) [1, 2, 1]"
value "count (2::int) [1, 2, 1]"
  
lemma count_leq_length: "count v xs \<le> length xs" 
  apply(induction xs)
   apply(auto)
  done
    
    (* exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]"
| "snoc (x # xs) e = Cons x (snoc xs e)"
  
value "snoc [1,2,4] 10 :: int list"
  
fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"
  
value "[1,2,3] @ [4,5] :: int list"
  
lemma reverse_snoc_is_cons_reverse[simp]: "reverse (snoc xs a) = a # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done 
    
    (* This needs lemma: reverse (snoc (reverse xs) a) = a # xs *)
lemma reverse_reverse_is_id[simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done
    
    (* exercise 2.5 *) 
fun sum_upto::"nat \<Rightarrow> nat" where 
  "sum_upto 0 = 0" 
| "sum_upto (Suc n) = (Suc n) + sum_upto n"
  
value "6 div 2 :: int"
value "5 div 2 :: int"
value "1 div 2 :: int"
  
lemma summation_formula_01[simp]: "sum_upto n = (n * (n+1)) div 2"
  apply(induction n)
   apply(auto)
  done   
    
end