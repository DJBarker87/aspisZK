import CuSavingsRetainedClaimBindingFinal
import CuSavingsRetainedCompositionGammaRho
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedClaimBindingGammaRho
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedClaimBindingFinal CuSavingsRetainedCompositionTx1Transport
variable [AspisR1CanonicalDots.Shared] [AspisR1RetainedClaimBinding.Trace]
  [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]

theorem tx1_binding_equivalence [AspisR1CuRho.HeapReserve] (common : PreparedCommon)
    (finish : Finish) {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase→Result Unit)) :
    (letI : PreparedCommon := binding true common
     retained.tx1 finish D publicValue publicBytes proof k hash obs)=
    (letI : PreparedCommon := binding false common
     retained.tx1 finish D publicValue publicBytes proof k hash obs) := by
  have hprep : @retained.tx1_prepare (binding true common) _ _ =
      @retained.tx1_prepare (binding false common) _ _ := by
    funext H D publicValue v hash obs initial
    exact tx1_prepare_equivalence common D publicValue v hash obs initial
  unfold retained.tx1
  rw [hprep]

variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]
/-- Actual original gamma preparation with original checked dot kernels to the
retained gamma/rho transaction with optimized kernels, in one source runtime.
The existing sufficient-allocation resource bound is explicit. -/
theorem source_tx1_equivalence {H : Type} (common : PreparedCommon)
    (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase→Result Unit))
    (backend : CuSavingsRhoEmptyReserveModel.Backend)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val) :
    letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
    (letI : PreparedCommon := binding false common
     retained.old_tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs)=
    (letI : PreparedCommon := binding true common
     retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs) := by
  letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
  calc
    (letI : PreparedCommon := binding false common
     retained.old_tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs)=
        (letI : PreparedCommon := binding false common
         retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs) := by
      letI : PreparedCommon := binding false common
      exact CuSavingsRetainedCompositionGammaRho.tx1_equivalence D publicValue publicBytes proof
        k hash obs backend start len cursor future h64 hfree
    _ = (letI : PreparedCommon := binding true common
         retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs) :=
      (tx1_binding_equivalence common (finishNew start len cursor) D publicValue publicBytes proof k hash obs).symm

#print axioms tx1_binding_equivalence
#print axioms source_tx1_equivalence
end AspisR1.CuSavingsRetainedClaimBindingGammaRho
