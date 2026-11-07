import RSL_Pool
set_option autoImplicit false
namespace LIB_BoxSpec
open RSL
/-- Source order common to the two CLOSED Box wrappers: decode, then allocate. -/
def law {A : Type} (decoded : Except ProgramError A) : RS A :=
 RS.bind (RS.ofExcept decoded) fun value =>
 RS.bind (RS.lift Spec.alloc) fun _ => RS.pure value
/-- Both allocation replies; a rejected decoder never allocates. -/
def observe {A : Type} (allocationReturns : Bool) (decoded : Except ProgramError A) :
    Obs (Except ProgramError A) :=
 match decoded with
 | .error e => ⟨.ret (.error e),[]⟩
 | .ok a => if allocationReturns then ⟨.ret (.ok a),[]⟩ else ⟨.abort,[]⟩
theorem cases {A : Type} (decoded : Except ProgramError A) (env : Env)
    (o : Obs (Except ProgramError A)) :
 law decoded env o ↔ o = observe true decoded ∨ o = observe false decoded := by
 cases decoded with
 | error e =>
   unfold law
   rw [RS.ofExcept_error,RS.bind_throw]
   simp only [RS.throw,Spec.pure,observe,or_self]
 | ok a =>
   unfold law
   rw [RS.ofExcept_ok,RS.bind_pure]
   change RS.seq (RS.lift Spec.alloc) (RS.pure a) env o ↔ _
   rw [RS.alloc_seq_iff]
   rfl
theorem member {A : Type} (decoded : Except ProgramError A) (reply : Bool) (env : Env) :
 law decoded env (observe reply decoded) := by
 apply (cases decoded env _).mpr
 cases reply with
 | false => exact Or.inr rfl
 | true => exact Or.inl rfl
theorem master_exact (L : PoolLib) (b : Bytes) :
 decodeMasterBox L b = law (match L.decodeMaster b with
   | some m => .ok m | none => .error .invalidAccountData) := by
 unfold decodeMasterBox law
 cases L.decodeMaster b <;> rfl
theorem checkpoint_exact (L : PoolLib) (b : Bytes) :
 decodeCheckpointBox L b = law (match L.decodeCheckpoint b with
   | some c => .ok c | none => .error .invalidAccountData) := by
 unfold decodeCheckpointBox law
 cases L.decodeCheckpoint b <;> rfl
#print axioms cases
#print axioms member
#print axioms master_exact
#print axioms checkpoint_exact
end LIB_BoxSpec
