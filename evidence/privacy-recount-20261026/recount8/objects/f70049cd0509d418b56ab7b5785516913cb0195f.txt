import R1Z.ProverRw18ContextCompression
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextReference
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

-- Arbitrary primitive dictionary, rather than only the closed selected one.
theorem loop (lambda : Q) (values : Slice U32) (out power : Q) :
    ProverRw18InlineContext.run lambda (⟨values,0⟩ : Iter) out power=
      PV_CompressList.fold values.val lambda out power := by
  rw [ProverRw18ContextInduction.run,PV_RW_NativeForList.initial,
    PV_RW_CompressNativeControl.listRun]
  change (do
    let state ← PV_RW_CompressStep.run (fun value state =>
      PV_RW_CompressEmission.generated.shipped_step state.1 state.2 value lambda) values.val (out,power)
    ok state.1)=_
  rw [PV_RW_CompressEmission.emitted_fold]
  rfl

theorem compress (tag : U32) (values : Slice U32) (lambda : Q) :
    ProverRw18ContextCompression.compress tag values lambda=
      ProverRwP6CompressSource.compress tag values lambda := by
  rw [PV_CompressModel.compress]
  unfold ProverRw18ContextCompression.compress
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro complex _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro out _
  rw [PV_RW_IteratorSource.start]
  simp only [bind_tc_ok]
  exact loop lambda values out lambda

#print axioms loop
#print axioms compress
end R1Z.ProverRw18ContextReference
