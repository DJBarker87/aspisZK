import R1Z.ProverRw18ContextInduction
import R1Z.PV_RW_NativeForList
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19P6RawContextIdentity
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

-- Isolate the generic list recursion from the closed arithmetic installation.
theorem listRun (step : U32 → Q × Q → Result (Q × Q))
    (values : List U32) (state : Q × Q) :
    PV_RW_ResultListRun.run step values state = PV_RW_CompressStep.run step values state := by
  induction values generalizing state with
  | nil => rfl
  | cons value tail ih =>
    change (do let next ← step value state; PV_RW_ResultListRun.run step tail next) = _
    change _ = (do let next ← step value state; PV_RW_CompressStep.run step tail next)
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

theorem loop (lambda : Q) (values : Slice U32) (out power : Q) :
    ProverRw18InlineContext.run lambda (⟨values,0⟩ : Iter) out power =
      PV_CompressList.fold values.val lambda out power := by
  rw [ProverRw18ContextInduction.run, PV_RW_NativeForList.initial, listRun]
  change (do
    let state ← PV_RW_CompressStep.run (fun value state =>
      PV_RW_CompressEmission.generated.shipped_step state.1 state.2 value lambda)
      values.val (out,power)
    ok state.1) = _
  rw [PV_RW_CompressEmission.emitted_fold]
  rfl

-- Literal initializer/iterator/inline-loop context. No primitive is stubbed.
-- It is not named or claimed to be the original whole-helper extraction.
-- The selected-dictionary bridge remains in ProverRw19P6ContextIdentity.
def context (tag : U32) (values : Slice U32) (lambda : Q) : Result Q := do
  let complex ← aspis_core.field.CM31.from_m31 tag
  let out ← aspis_core.field.QM31.from_cm31 complex
  let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
  ProverRw18InlineContext.run lambda iterator out lambda

theorem context_eq_source (tag : U32) (values : Slice U32) (lambda : Q) :
    context tag values lambda = ProverRwP6CompressSource.compress tag values lambda := by
  rw [PV_CompressModel.compress]
  unfold context
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro complex _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro out _
  rw [PV_RW_IteratorSource.start]
  simp only [bind_tc_ok]
  exact loop lambda values out lambda

theorem identity (ops : ExternalFuns) :
    @ProverRwP6CompressSource.compress _ ops = @context _ ops := by
  funext tag values lambda
  exact (@context_eq_source _ ops tag values lambda).symm

#print axioms listRun
#print axioms loop
#print axioms context_eq_source
#print axioms identity
end R1Z.ProverRw19P6RawContextIdentity
