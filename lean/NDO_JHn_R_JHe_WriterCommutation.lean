import RPz7_WAdm_Execution
import RPz7_Uni_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_WriterCommutation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev Writer := {H : Type} → aspis_core.digest.Digest32 H → verifier.Prepared →
  verifier.Accumulator → Slice U8 → Slice U8 → H → Result (alloc.vec.Vec U8)

theorem row (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (w : Writer) :
    RowShape_InstalledSlots.verifierOps {ops with op16:=w} B std=
      {RowShape_InstalledSlots.verifierOps ops B std with op16:=w} := by
  cases ops
  rfl
#print axioms row

theorem shape (ops : Ops) (w : Writer) :
    Op3I_Install.install {ops with op16:=w}={Op3I_Install.install ops with op16:=w} := by
  cases ops
  rfl
#print axioms shape

theorem scan (ops : Ops) (w : Writer) :
    Op4P_Install.install {ops with op16:=w}={Op4P_Install.install ops with op16:=w} := by
  cases ops
  rfl
#print axioms scan

theorem actual {C : Type} (ops : Ops) (r : Bool) (q : Port3_NativeQueryBody.Ops)
    (g : Port3_NativeGeometryBody.Ops C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    WAdm_Execution.actual ops r q g B std=
      {Tx1Q_Execution.actual ops r q g B std with op16:=WAdm_Install.writer} := by
  unfold WAdm_Execution.actual WAdm_Execution.base WAdm_Install.base
  rw [scan,shape,row]
  rfl
#print axioms actual
end AspisR1.JHe_WriterCommutation
end
