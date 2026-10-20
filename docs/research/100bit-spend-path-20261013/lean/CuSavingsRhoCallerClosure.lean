import CuSavingsRhoTransactions
import CuSavingsRhoEntryTransport
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoCallerClosure
open Aeneas Aeneas.Std Result AspisR1RhoTransactions
open CuSavingsRhoEmptyReserveModel CuSavingsRhoEntryTransport
variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
variable [AspisR1RhoPowerTail.PreparedCommon] [AspisR1CuRho.ScalarKBlocks]
variable [AspisR1RhoResumeCaller.ResumeCommon] [TxCommon]

/-- Actual caller-derived source preparation and constructor results supply all
fresh-entry arithmetic premises. The complete checkpoint-producing caller is
then equivalent; no canonical-input or coefficient-equivalence law is assumed. -/
theorem fresh_source_equivalence {H : Type}
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
    (v : verifier.View) (public1 proof : Slice U8) (k : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (hk : k.val ≤ 22) :
    letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    tx_new.tx1_finish digest v (prepared sourcePrepared) (accumulator sourceAccumulator)
      (array wide finalScratch) public1 proof k hash obs =
    tx_old.tx1_finish digest v (prepared sourcePrepared) (accumulator sourceAccumulator)
      (array wide finalScratch) public1 proof k hash obs := by
  have hr := preparation_input sourceDigest sem sourceView hash scratch finalScratch sourcePrepared hprep
  obtain ⟨hc,hp,hl⟩ := constructor_inputs backend sourceView.variant sourceAccumulator hnew
  exact CuSavingsRhoTransactions.tx1_finish_equivalence digest start len cursor future h64 hfree
    v (prepared sourcePrepared) (accumulator sourceAccumulator) (array wide finalScratch)
    public1 proof k hash obs hk hr hp hc hl

#print axioms fresh_source_equivalence
end AspisR1.CuSavingsRhoCallerClosure
