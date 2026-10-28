import R1Z.PV_RunJoin_RuntimeMemorySource38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_MemoryZero
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes] {W S F D DF ZF C : Type}
theorem complete (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (N : Usize) (v : Array U8 N) (w : W) :
    (PV_RunJoin_RuntimeMemory38.algebra base m).zeroArray N v w =
      ⟨PV_W_SourceSyntax.resultOutcome
          ((PV_RunJoin_RuntimeMemorySource38.selected ops m w).op122 PV_FXM_ZeroSelected.byteZero v),
        m.zeroCommit w (PV_FXM_ZeroWorld.indexed (m.arrayAddress w v) 0 N.val (m.zeroView w)),
        [(w,none)]⟩ := by
  apply Run.ext
  · exact PV_RunJoin_RuntimeMemorySource38.array ops base m N v w
  · exact PV_W_MemoryLift.zero_world m.zeroView m.zeroCommit (m.arrayAddress w v) N w
  · rfl
#print axioms complete
end R1Z.PV_RJDec_MemoryZero
