import CuSavingsRetainedCompositionGammaTx1
import CuSavingsRetainedCompositionTx1
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionGammaRho
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedCompositionTx1Transport
variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]

/-- Two interacting source replacements are now in one computational source
interpretation: original gamma prefix/caller and actual old/new rho stages.
There is no per-stage equivalence, successful producer, or canonicality premise.
The immutable-claim binder interpretation and numeric runtime budget remain
explicit source/runtime boundaries, documented by the source emission audit. -/
theorem tx1_equivalence {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (backend : CuSavingsRhoEmptyReserveModel.Backend)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val) :
    letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
    retained.old_tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs=
      retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs := by
  letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
  calc
    retained.old_tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs=
        retained.tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs :=
      CuSavingsRetainedCompositionGammaTx1.source_eq_of_claim_factor (finishOld start len cursor)
        D publicValue publicBytes proof k hash obs (fun _ _ _ _ => rfl)
    _ = retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs :=
      (CuSavingsRetainedCompositionTx1.source_tx1_rho_equivalence D publicValue publicBytes proof
        k hash obs backend start len cursor future h64 hfree).symm

/-- Any source-model observation of the complete computation is preserved.
The caller chooses the existing model observation; this introduces no new
operational semantics or discarded application-effect field. -/
theorem observations_eq {Observation : Type}
    (observe : Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) → Observation)
    {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (backend : CuSavingsRhoEmptyReserveModel.Backend)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val) :
    letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
    observe (retained.old_tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs)=
      observe (retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs) := by
  exact congrArg observe (tx1_equivalence D publicValue publicBytes proof k hash obs
    backend start len cursor future h64 hfree)

#print axioms tx1_equivalence
#print axioms observations_eq
end AspisR1.CuSavingsRetainedCompositionGammaRho
