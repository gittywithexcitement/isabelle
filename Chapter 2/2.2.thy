theory 2
  imports Main
begin
  
  (* The long arrow (\<Longrightarrow>) separates assumptions (on the left) from the conclusion. *)
  
value "1+2::nat"
value "1+2::int"
value "1-2::nat" (* NB: 0, not -1 *)
value "1-2::int"
  
  (* exercise 2.2 *)
datatype nat = Zero | Suc nat
  
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "add Zero n = n" 
| "add (Suc l) r = Suc(add l r)"
  
lemma add_Zero_is_id[simp]: "add l Zero = l"
  apply(induction l)
   apply(auto)
  done
    
theorem add_is_associative: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done
    
    (* the '[simp]' is required, otherwise this lemma is not used by 'auto' in the theorem below
If you ask sledgehammer, it will tell you:
  by (simp add: add_in_reverse)
 *)
lemma add_in_reverse[simp]: "Suc (add y x) = add y (Suc x)"
  apply(induction y)
   apply(auto)
  done 
    
theorem add_is_commutative: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done
    
fun double :: "nat \<Rightarrow> nat" where 
  "double Zero = Zero" 
| "double (Suc x) = Suc (Suc (double x))"
  
lemma double_is_add_to_self: "double x = add x x"  
  apply(induction x)
   apply(auto)
  done
    
    (* exercise 2.3 *) 
    
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where 
  "count v Nil = Zero" 
| "count v (Cons x xs) = (if v=x then Suc (count v xs) else count v xs)"
  
value "count (1::int) [1, 2, 1]"
value "count (2::int) [1, 2, 1]"
  
lemma count_leq_length: "count a xs \<le> length xs"
  
  
end