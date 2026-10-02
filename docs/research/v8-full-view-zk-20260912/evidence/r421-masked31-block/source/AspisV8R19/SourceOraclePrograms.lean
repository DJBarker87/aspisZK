import AspisV8R19.OracleFiniteSupport
import AspisV8R19.SourceDuplexStep

/-! Byte-exact transcript primitives as causal programs. Addresses and full
32-byte replies share one oracle. The complete source sampler/prover compiler
is still separate; no independently random squeeze stream is substituted. -/
set_option autoImplicit false
namespace AspisV8R19.SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps OracleFiniteSupport OracleResampling
open DuplexFrames SourceDuplexStep

def squeezeProgram (s : State) : Program Bytes State (State × State) :=
  .ask (squeeze (bytes s)) (fun out =>
    .ask (advance (bytes s)) (fun next => .done (out,next)))

def absorbProgram (s : State) (label : Byte) (data : Bytes) : Program Bytes State State :=
  .ask (absorb (bytes s) label data) Program.done

theorem squeeze_eval (H : Bytes → State) (s : State) :
    eval H (squeezeProgram s) = (calls H s,step H s) := rfl

theorem absorb_eval (H : Bytes → State) (s : State) (label : Byte) (data : Bytes) :
    eval H (absorbProgram s label data) =
      ([(absorb (bytes s) label data,H (absorb (bytes s) label data))],
        H (absorb (bytes s) label data)) := rfl

theorem absorb_two_same_address (s : State) (label : Byte) (first second : Bytes) :
    absorb (bytes s) label (first ++ second) =
      bytes s ++ [0,label] ++ first ++ second := by simp [absorb,List.append_assoc]

def squeezeBlocks : ℕ → State → Program Bytes State (List State × State)
  | 0,s => .done ([],s)
  | n+1,s => bind (squeezeProgram s) (fun pair =>
      bind (squeezeBlocks n pair.2) (fun tail => .done (pair.1::tail.1,tail.2)))

theorem squeeze_blocks_call_count (H : Bytes → State) (n : ℕ) (s : State) :
    (eval H (squeezeBlocks n s)).1.length = 2*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [squeezeBlocks,eval_bind,squeeze_eval,eval,List.append_nil]
      simp [calls,ih,Nat.mul_succ,Nat.add_comm] <;> omega

theorem squeeze_blocks_output_count (H : Bytes → State) (n : ℕ) (s : State) :
    (eval H (squeezeBlocks n s)).2.1.length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [squeezeBlocks,eval_bind,squeeze_eval,eval,List.length_cons]
      rw [ih]

/-- The finite support includes every possible advance answer, including a
return to the old state. Repeated addresses are handled by lazyMean's cache. -/
theorem blocks_memoized_law (n : ℕ) (s fallback : State)
    (observe : View Bytes State (List State × State) → ℚ) :
    let p := squeezeBlocks n s
    mean (fun H : {i // i ∈ support p} → State =>
      observe (eval (extend (support p) H fallback) p)) =
      lazyMean p (fun _ => none) observe := by
  exact finite_support_oracle_law (squeezeBlocks n s) _ (fun _ h => h) fallback observe

theorem source_primitive_continuation_eval {O : Type}
    (s : State) (label : Byte) (data : Bytes)
    (next : (State × State) → Program Bytes State O) (H : Bytes → State) :
    eval H (bind (absorbProgram s label data) (fun advanced =>
      bind (squeezeProgram advanced) next)) =
      let advanced := H (absorb (bytes s) label data)
      let tail := eval H (next (step H advanced))
      ([(absorb (bytes s) label data,advanced)] ++ calls H advanced ++ tail.1,tail.2) := by
  simp only [eval_bind,absorb_eval,squeeze_eval,List.append_assoc]

/-- Applying this to the program in source_primitive_continuation_eval gives
its full law without elaborating the enormous concrete 32-byte branch set. -/
theorem byte_program_law {O : Type} (p : Program Bytes State O) (fallback : State)
    (observe : View Bytes State O → ℚ) :
    mean (fun H : {i // i ∈ support p} → State =>
      observe (eval (extend (support p) H fallback) p)) =
      lazyMean p (fun _ => none) observe := by
  exact finite_support_oracle_law p _ (fun _ h => h) fallback observe

#print axioms squeeze_eval
#print axioms absorb_eval
#print axioms absorb_two_same_address
#print axioms squeeze_blocks_call_count
#print axioms squeeze_blocks_output_count
#print axioms blocks_memoized_law
#print axioms source_primitive_continuation_eval
#print axioms byte_program_law
end AspisV8R19.SourceOraclePrograms
