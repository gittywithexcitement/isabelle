(* exercise 3.11 *)
theory ASMReg
  imports 
    AExp "~~/src/HOL/Library/Code_Target_Nat" 
begin
  
section "Register Machine and Compilation"
subsection "Register Machine"
  
  (* A register identifier is a natural number. I.e. the registers are numbered 0, 1, ...  *)
type_synonym reg = nat
  
datatype instr = 
  LDI int reg | (* store integer in register *) 
  LD vname reg | (* take variable from current state, store in register *)
  ADD reg reg (* add right register to left, store in left *)
  
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> (reg \<Rightarrow> int)" where
  "exec1 (LDI ii ir) _ registers = (registers (ir := ii))" |
  "exec1 (LD iv ir) state registers = (registers (ir := (state iv)))" | 
  "exec1 (ADD r\<^sub>d r\<^sub>s) _ registers = (registers (r\<^sub>d := (registers r\<^sub>d) + (registers r\<^sub>s)))"
  
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> (reg \<Rightarrow> int)" where
  "exec [] _ registers = registers" | 
  "exec (i#is) state registers = exec is state (exec1 i state registers)" 

subsection "Compilation"
  
  (* The compiler takes an arithmetic expression a and a register r and produces a list of
instructions whose execution places the value of a into r. The registers > r should be used in a
stack-like fashion for intermediate results, the ones < r should be left alone. *)
fun compile :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "compile (N n) r\<^sub>d = [LDI n r\<^sub>d]" |
  "compile (V v) r\<^sub>d = [LD v r\<^sub>d]" |
  "compile (Plus e\<^sub>1 e\<^sub>2) r\<^sub>d = (let
    left = compile e\<^sub>1 r\<^sub>d;
    right = compile e\<^sub>2 (r\<^sub>d + 1)
  in left @ right @ [ADD r\<^sub>d (r\<^sub>d + 1)])"
  
value "compile (Plus (N 9) (N 10)) 0"
value "exec (compile (Plus (N 9) (N 10)) 1) <> <> 1"
  
  (* Do I need a lemma stating that compile does not change registers less than the argument it was given? *)
  
theorem compile_is_correct:"exec (compile expr reg_dest) state rs reg_dest = aval expr state"
  (* possibly arbitrary: reg_dest state rs *)
  (* apply(induction expr) *)
  (* I think reg_dest should be arbitrary because it changes during compile *)
  apply(induction expr arbitrary: reg_dest)
    apply(simp_all)
    (* try  *)
    (* apply(auto)  *)
    (* by (auto) *)
  sorry
    
end