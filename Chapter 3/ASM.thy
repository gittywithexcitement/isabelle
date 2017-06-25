(* theory ASM imports AExp begin *)
theory ASM imports AExp Option begin
  
section "Stack Machine and Compilation"
subsection "Stack Machine"
  
text_raw{*\snip{ASMinstrdef}{0}{1}{% *}
datatype instr = LOADI val | LOAD vname | ADD
text_raw{*}%endsnip*}
  
text_raw{*\snip{ASMstackdef}{1}{2}{% *}
type_synonym stack = "val list"
text_raw{*}%endsnip*}
  
abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"
  
text{* \noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist.*}
  
text_raw{*\snip{ASMexeconedef}{0}{1}{% *}
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1 (LOADI n) _ stk  = Some (n # stk)" |
  "exec1 (LOAD x) s stk  =  Some (s(x) # stk)" |
  "exec1  ADD _ (h0 # h1 # stk)  = Some ((h0 + h1) # stk)"|
  "exec1  ADD _ _ = None"
text_raw{*}%endsnip*}
  
text_raw{*\snip{ASMexecdef}{1}{2}{% *}
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec [] _ stk = Some stk" |
  "exec (i#is) s stk = (case (exec1 i s stk) of
    Some stk1 \<Rightarrow> exec is s stk1
    |None \<Rightarrow> None)"
  (* "exec (i#is) s stk = exec is s (exec1 i s stk)" *)
text_raw{*}%endsnip*}
  
value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"
  
value "map_option (exec [ADD] <>) (None)"
value "map_option (exec [ADD] <>) (Some [1,2])"
(* value "map_option (exec [ADD] <>) ( [1,2])" ERROR*)
(* value "Option.bind (Some [1,2]) (map_option (exec [ADD] <>))" ERROR*)
value "Option.bind (Some [1,2]) ((exec [ADD] <>))"
  
(*qualified primrec bind :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"
where
  bind_lzero: "bind None f = None"
| bind_lunit: "bind (Some x) f = f x" *)
  
  (* "map_option f y = (case y of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x))" *)
lemma exec_append[simp]:
  "exec (is1@is2) s stk = Option.bind (exec is1 s stk) (exec is2 s)"
  (* "exec (is1@is2) s stk = map_option (exec is2 s) (exec is1 s stk)" ERROR *)
  (* "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)" *)
  apply(induction is1 arbitrary: stk)
   apply(simp)
  apply(simp)
  by (simp add: option.case_eq_if)
    
subsection "Compilation"
  
text_raw{*\snip{ASMcompdef}{0}{2}{% *}
fun compile :: "aexp \<Rightarrow> instr list" where
  "compile (N n) = [LOADI n]" |
  "compile (V x) = [LOAD x]" |
  "compile (Plus e\<^sub>1 e\<^sub>2) = compile e\<^sub>1 @ compile e\<^sub>2 @ [ADD]"
text_raw{*}%endsnip*}
  
value "compile (Plus (Plus (V ''x'') (N 1)) (V ''z''))"
  
theorem exec_compile: "exec (compile a) s stk = Some (aval a s # stk)"
  apply(induction a arbitrary: stk)
  by (auto)
  
    
end