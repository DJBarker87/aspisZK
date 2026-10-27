import R1Z.PV_RW_CompressClosed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressClosedTotal
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem fold (values : List U32) (lambda : Q) (state : Q × Q) :
    ∃ next, PV_RW_CompressClosedFold.fold values lambda state = ok next := by
  induction values generalizing state with
  | nil => exact ⟨state,rfl⟩
  | cons value values ih =>
    obtain ⟨next,hs⟩ := PV_RW_CompressConcrete.total state.1 state.2 value lambda
    obtain ⟨last,hl⟩ := ih next
    refine ⟨last,?_⟩
    change (do
      let next ← PV_RW_CompressConcrete.step state.1 state.2 value lambda
      PV_RW_CompressClosedFold.fold values lambda next) = _
    rw [hs]
    exact hl

theorem compress (tag : U32) (values : Slice U32) (lambda : Q) :
    ∃ out, PV_RW_CompressClosed.compress tag values lambda = ok out := by
  obtain ⟨last,hl⟩ := fold values.val lambda (PV_RW_CompressLiftSelectors.initial tag,lambda)
  refine ⟨last.1,?_⟩
  simp only [PV_RW_CompressClosed.compress,hl,bind_tc_ok]

theorem owned_equal (tag : U32) (values : Slice U32) (lambda : Q) :
    PV_RW_CompressClosed.compress tag values lambda = PV_RW_CompressClosed.owned tag values lambda := by
  simp only [PV_RW_CompressClosed.compress,PV_RW_CompressClosed.owned,
    PV_RW_CompressClosedFold.fold,PV_RW_CompressClosedFold.owned,PV_RW_CompressConcrete.current_owned]

theorem owned (tag : U32) (values : Slice U32) (lambda : Q) :
    ∃ out, PV_RW_CompressClosed.owned tag values lambda = ok out := by
  rw [← owned_equal]
  exact compress tag values lambda
#print axioms fold
#print axioms compress
#print axioms owned_equal
#print axioms owned
end R1Z.PV_RW_CompressClosedTotal
