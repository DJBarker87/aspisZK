import PV_FN_THREAD_f6PrefixFrames
import PV_THR2_InterpreterAgreement
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6PrefixTransport
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6Interfaces

/-- Proof-local instruction agreement along the source trace. Concrete provider
instances must discharge this from their installed definitions and source shapes;
it is never a replacement callee contract or a privacy endpoint premise. -/
def Agreement {E : Type} (M N : Machine E) (x : Entry E) : Prop :=
  ∀ n, PV_THR2_TableIntrinsic.Agree M.programs N.programs (run M x n) ∧
    PV_THR2_InterpreterAgreement.NativeAgree M.handler N.handler (run M x n)

/-- Reuse the symbolic instruction-shape induction once for every prefix,
including cutoffs inside callees, failures and running pending configurations.
No concrete provider Agreement instance is asserted here. -/
theorem all_prefixes {E : Type} (M N : Machine E) (x : Entry E)
    (carrier : M.carrier = N.carrier) (control : M.control = N.control)
    (agreement : Agreement M N x) : ∀ n, run M x n = run N x n := by
  intro n
  unfold run
  rw [← carrier,← control]
  exact (PV_THR2_InterpreterAgreement.run M.carrier M.control M.programs N.programs
    M.handler N.handler n (entry x) (fun k _ => agreement k)).symm

/-- The first restoration boundary is preserved in BOTH directions. -/
theorem before_return {E : Type} (M N : Machine E) (x : Entry E)
    (equal : ∀ n, run M x n = run N x n) (n : Nat) :
    BeforeReturn M x n ↔ BeforeReturn N x n := by
  constructor
  · intro before k hk
    rw [← equal k]
    exact before k hk
  · intro before k hk
    rw [equal k]
    exact before k hk

/-- Transport the complete prefix contract, rather than only its Reached
endpoint. Argument footprints, full store and OWNER byte frames are transported
by name; no callee prefix can be omitted from the source FullPost obligation. -/
theorem full_post {E : Type} (M N : Machine E) (x : Entry E)
    (valuePost : Store Data → PV_EVHB_OwnerMachine.OWNER → Data → Prop)
    (carrier : M.carrier = N.carrier) (equal : ∀ n, run M x n = run N x n)
    (source : FullPost M x valuePost) : FullPost N x valuePost := by
  intro n before
  have sourceBefore := (before_return M N x equal n).mpr before
  have atPrefix := source n sourceBefore
  dsimp only at atPrefix ⊢
  rw [← equal n]
  rcases atPrefix with ⟨defined,store,owner,wellformed,events,completed,restored⟩
  exact ⟨defined,PV_FN_THREAD_f6PrefixFrames.store_frame M N carrier x _ store,
    PV_FN_THREAD_f6PrefixFrames.owner_frame M N carrier x _ owner,
    wellformed,events,completed,restored⟩

#print axioms all_prefixes
#print axioms before_return
#print axioms full_post
end PV_FN_THREAD_f6PrefixTransport
