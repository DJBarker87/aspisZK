import R1Z.PV_RunJoin_RuntimeMemorySource38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_MemoryDrop
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes] {W S F D DF ZF C : Type}
theorem complete (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (v : alloc.vec.Vec U32) (w : W) :
    (PV_RunJoin_RuntimeMemory38.algebra base m).dropWords v w =
      ⟨PV_W_SourceSyntax.resultOutcome
          ((PV_RunJoin_RuntimeMemorySource38.selected ops m w).op4 v),
        m.dropCommit w (PV_FXM_DropWorld.reference m.free (m.dropBuffer w v) (m.dropView w)).2,
        [(w,none)]⟩ := by
  apply Run.ext
  · exact PV_RunJoin_RuntimeMemorySource38.drop ops base m v w
  · exact PV_W_MemoryLift.drop_world m.dropView m.dropCommit m.free (m.dropBuffer w v) w
  · rfl
#print axioms complete
end R1Z.PV_RJDec_MemoryDrop
