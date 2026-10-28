import R1Z.PV_RunJoin_RuntimeMemorySource38
import R1Z.PV_RJDec_Run
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_MemoryReserve
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes] {W S F D DF ZF C T : Type}

/-- Whole installed reservation record. Allocation refusal and overflow are
inner Results; their post-world and the original call remain present. Runtime
metadata, allocator and commit still require their native associations. -/
theorem complete (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize) (w : W) :
    (PV_RunJoin_RuntimeMemory38.algebra base m).reserve Allocator v n w =
      let e := PV_FXM_ReserveWorld.reference m.allocate m.wordMax m.byteMax
        (m.shape T) (PV_FXM_ReserveSelected.buffer v (m.metadata w v)) n.val (m.reserveView w)
      ⟨PV_W_SourceSyntax.resultOutcome
          ((PV_RunJoin_RuntimeMemorySource38.selected ops m w).op32 Allocator v n),
        m.reserveCommit w e.buffer e.world,[(w,none)]⟩ := by
  apply PV_RJDec_Run.ext
  · exact PV_RunJoin_RuntimeMemorySource38.reserve ops base m Allocator v n w
  · exact PV_RunJoin_RuntimeMemory38.reserve base m Allocator v n w
  · rfl
#print axioms complete
end R1Z.PV_RJDec_MemoryReserve
