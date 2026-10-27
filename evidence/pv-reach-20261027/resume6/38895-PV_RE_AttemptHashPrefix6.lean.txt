import R1Z.PV_RE_PublicPrefix6
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AttemptHashPrefix6
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes]
def publicFrame (bytes : alloc.vec.Vec U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 1#usize [alloc.vec.Vec.deref bytes])

/-- The first actual supplied-hash invocation in the original attempt,
following the successful original public serialization call. -/
theorem attempt_to_hash (D : ExternalFuns) (pub : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (secret : Secrets) (store : Store)
    (bytes : alloc.vec.Vec U8)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes)) :
    ∃ next,
      @prover.prove_masked_attempt _ D pub compiled variant hash secret store =
        (hash (publicFrame bytes) >>= next) := by
  letI : ExternalFuns := D
  unfold prover.prove_masked_attempt
  have call_eq :
      @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes _ D pub =
      D.op226 pub := rfl
  rw [call_eq, serialization]
  change ∃ next, (D.op12
    prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
    (.Ok bytes) () >>= _) = (hash (publicFrame bytes) >>= next)
  rw [map_error]
  exact ⟨_,rfl⟩

#print axioms publicFrame
#print axioms attempt_to_hash
end R1Z.PV_RE_AttemptHashPrefix6
