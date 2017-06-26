(* exercise 3.12 *)
theory ASMReg0
  imports 
    AExp "~~/src/HOL/Library/Code_Target_Nat" 
begin
  
section "Register Machine and Compilation"
subsection "Register Machine"
  
  (* A register identifier is a natural number. I.e. the registers are numbered 0, 1, ...  *)
type_synonym reg = nat
  
(* exercise 3.12 *)
datatype instr = 
  LDI0 val | (* register 0 is the target *)
  LD0 vname | (* register 0 is the target *)
  MV0 reg | (* register 0 is the source *)
  ADD0 reg (* register 0 is the target, and an operand *)
  
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> (reg \<Rightarrow> int)" where
  "exec1 (LDI0 val) _ registers = (registers (0 := val))" |
  "exec1 (LD0 vname) state registers = registers (0 := state vname)" |
  "exec1 (MV0 reg) _ registers = registers (reg := registers 0)" |
  "exec1 (ADD0 reg\<^sub>o\<^sub>p) _ registers = registers (0 := registers 0 + registers reg\<^sub>o\<^sub>p)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> (reg \<Rightarrow> int)" where
  "exec [] _ registers = registers" | 
  "exec (i#is) state registers = exec is state (exec1 i state registers)"

lemma exec_append:"exec (l1 @ l2) s rs = exec l2 s (exec l1 s rs)"
  (* rs MUST be arbitrary. This strengthens the induction hypothesis: the register
    file in the IH may be different than the register file in the thesis. 
    This is necessary, because the inductive step adds another instruction, which will cause the
    register file to change when executed. That is, the register file in the inductive step will be
    different than the register file in the IH, because of the inductive step. *)
  apply(induction l1 arbitrary: rs)
   by(simp_all)

subsection "Compilation"
  
  (* The compiler takes an arithmetic expression a and produces a list of
instructions whose execution places the value of a into register 0. 
TODO The registers > r should be used in a
stack-like fashion for intermediate results. *)
fun compile :: "aexp \<Rightarrow> instr list" where
  "compile (N n) = [LDI0 n]" |
  "compile (V v) = [LD0 v]" |
  "compile (Plus e\<^sub>1 e\<^sub>2) = (let
    left = compile e\<^sub>1;
    right = compile e\<^sub>2
  in left @ MV0 1 @ right @ [ADD0 1])"
  (* LDI0 val | (* register 0 is the target *) *)
  (* LD0 vname | (* register 0 is the target *) *)
  (* MV0 reg | (* register 0 is the source *) *)
  (* ADD0 reg (* register 0 is the target, and an operand *) *)
  
value "compile (Plus (N 9) (N 10)) 0"
value "exec (compile (Plus (N 9) (N 10)) 1) <> <> 1"
  
lemma lesser_registers_unchanged:
  "reg\<^sub>q\<^sub>u\<^sub>e\<^sub>r\<^sub>y < reg\<^sub>d\<^sub>e\<^sub>s\<^sub>t \<Longrightarrow> 
    (exec (compile exp reg\<^sub>d\<^sub>e\<^sub>s\<^sub>t) st rs) reg\<^sub>q\<^sub>u\<^sub>e\<^sub>r\<^sub>y = rs reg\<^sub>q\<^sub>u\<^sub>e\<^sub>r\<^sub>y"
  (* arbitrary reg\<^sub>d\<^sub>e\<^sub>s\<^sub>t is required because it changes when compiling ADD
    arbitrary rs is required because it changes when executing *)
  apply(induction exp arbitrary: rs reg\<^sub>d\<^sub>e\<^sub>s\<^sub>t)
    apply(simp_all)
  using exec_append by simp

theorem compile_is_correct: "exec (compile expr reg_dest) state rs reg_dest = aval expr state"
  (* reg_dest is arbitrary because it changes during compile ADD
    rs is arbitrary because it changes during exec*)
  apply(induction expr arbitrary: reg_dest rs)
    apply(simp_all)
  using exec_append lesser_registers_unchanged by simp
    
  
end