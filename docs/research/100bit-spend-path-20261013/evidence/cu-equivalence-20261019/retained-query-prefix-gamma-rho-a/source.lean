import CuSavingsRetainedQueryPrefixTx1
import CuSavingsRetainedClaimBindingGammaRho
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixGammaRho
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedQueryPrefixBinding CuSavingsRetainedCompositionTx1Transport
variable [AspisR1CanonicalDots.Shared] [AspisR1RetainedClaimBinding.Trace]
  [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoResumeCaller.ResumeCommon]
  [AspisR1RhoTransactions.TxCommon]
attribute [local irreducible] finishNew finishOld CuSavingsRetainedQueryPrefixFinishAdapter.finish

theorem source_tx1_equivalence {H : Type} (prepared : PreparedCommon)
    (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries) (dot : AspisR1RetainedDots.Shared)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H) (obs : Option (verifier.Phase→Result Unit))
    (backend : CuSavingsRhoEmptyReserveModel.Backend) (start len cursor : Usize)
    (future : Nat) (h64 : UScalarTy.Usize.numBits=64) (hfree : start.val+8+8199+future≤cursor.val) :
    letI : AspisR1CuRho.HeapReserve:=CuSavingsRhoEmptyReserveModel.heapReserve backend
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     letI : PreparedCommon:=CuSavingsRetainedClaimBindingFinal.binding false prepared
     retained.old_tx1 (finishOld start len cursor) D pub publicBytes proof k hash obs)=
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     letI : PreparedCommon:=CuSavingsRetainedClaimBindingFinal.binding true prepared
     retained.tx1 (finishNew start len cursor) D pub publicBytes proof k hash obs) := by
  letI : AspisR1CuRho.HeapReserve:=CuSavingsRhoEmptyReserveModel.heapReserve backend
  calc
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     letI : PreparedCommon:=CuSavingsRetainedClaimBindingFinal.binding false prepared
     retained.old_tx1 (finishOld start len cursor) D pub publicBytes proof k hash obs)=
      (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
       letI : PreparedCommon:=CuSavingsRetainedClaimBindingFinal.binding true prepared
       retained.tx1 (finishNew start len cursor) D pub publicBytes proof k hash obs) := by
        letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
        exact CuSavingsRetainedClaimBindingGammaRho.source_tx1_equivalence prepared D pub publicBytes proof k hash obs
          backend start len cursor future h64 hfree
    _ = (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
         letI : PreparedCommon:=CuSavingsRetainedClaimBindingFinal.binding true prepared
         retained.tx1 (finishNew start len cursor) D pub publicBytes proof k hash obs) := by
      letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
      have h:=CuSavingsRetainedQueryPrefixTx1.source_equivalence
        (CuSavingsRetainedClaimBindingFinal.binding true prepared) common B dot start len cursor
        D pub publicBytes proof k hash obs
      exact h.symm

#print axioms source_tx1_equivalence
end AspisR1.CuSavingsRetainedQueryPrefixGammaRho
