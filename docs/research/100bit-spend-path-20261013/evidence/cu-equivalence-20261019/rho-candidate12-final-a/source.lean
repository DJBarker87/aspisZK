import CuSavingsRhoCallerClosure
import CuSavingsRhoCryptographicTrace
import CuSavingsRhoResourceAdmission
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoCandidate12
open Aeneas Aeneas.Std Result AspisR1RhoTransactions
open CuSavingsRhoEmptyReserveModel CuSavingsRhoEntryTransport
variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
variable [AspisR1RhoPowerTail.PreparedCommon] [AspisR1CuRho.ScalarKBlocks]
variable [AspisR1RhoResumeCaller.ResumeCommon] [TxCommon]

/-- Final source-consuming result. Each numerical resource condition applies
at the extra reservation boundary; parameters can be instantiated separately
for the actual transaction runs. Equality includes errors and divergence.
Ordered hash-call projection is audited separately below, using identical
prefix source and the proved equal invocation schedule. -/
theorem all_callers_equivalence {H : Type}
    (digest : aspis_core.Digest32 H) (sourceDigest : AspisR1RhoPowerTail.aspis_core.Digest32 H)
    (sem : AspisR1RhoPowerTail.r1_semantic.Verified H)
    (sourceView : AspisR1RhoPowerTail.verifier.View) (hash : H)
    (scratch finalScratch : Array T.E 29#usize) (sourcePrepared : T.Prep)
    (backend : Backend) (sourceAccumulator : T.Acc)
    (hprep : AspisR1RhoPowerTail.gamma_new.Prepared.gamma_new_new sourceDigest sem sourceView hash scratch =
      .ok (.Ok sourcePrepared,finalScratch))
    (hnew : @AspisR1RhoPowerTail.verifier.Accumulator.new (heapReserve backend)
      sourceView.variant = .ok (.Ok sourceAccumulator))
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val)
    (v : verifier.View) (public1 proof checkpoint1 : Slice U8) (k : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (hk : k.val ≤ 22) :
    (letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    tx_new.tx1_finish digest v (prepared sourcePrepared) (accumulator sourceAccumulator)
      (array wide finalScratch) public1 proof k hash obs =
    tx_old.tx1_finish digest v (prepared sourcePrepared) (accumulator sourceAccumulator)
      (array wide finalScratch) public1 proof k hash obs) ∧
    (letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
      tx_new.tx2 digest public1 proof checkpoint1 hash obs =
        tx_old.tx2 digest public1 proof checkpoint1 hash obs) ∧
    (letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
      tx_new.tx2_authenticated digest public1 proof checkpoint1 hash obs =
        tx_old.tx2_authenticated digest public1 proof checkpoint1 hash obs) := by
  refine ⟨?_,?_,?_⟩
  · exact CuSavingsRhoCallerClosure.fresh_source_equivalence digest sourceDigest sem sourceView hash
      scratch finalScratch sourcePrepared backend sourceAccumulator hprep hnew start len cursor future h64 hfree
      v public1 proof k obs hk
  · exact CuSavingsRhoTransactions.tx2_equivalence digest start len cursor future h64 hfree public1 proof checkpoint1 hash obs
  · exact CuSavingsRhoTransactions.tx2_authenticated_equivalence digest start len cursor future h64 hfree public1 proof checkpoint1 hash obs

#print axioms all_callers_equivalence
#print axioms CuSavingsRhoCryptographicTrace.expanded_trace_equivalence
#print axioms CuSavingsRhoResourceAdmission.layout_admitted
#print axioms CuSavingsRhoAllocationSuccess.initializer_success
end AspisR1.CuSavingsRhoCandidate12
