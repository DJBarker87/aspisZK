import CuSavingsRetainedClaimBindingPrepared
import CuSavingsRetainedClaimBindingSelector
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedClaimBindingFinal
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
variable [AspisR1CanonicalDots.Shared] [AspisR1RetainedClaimBinding.Trace]
  [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
@[reducible] def binding (isNew : Bool) (common : PreparedCommon) : PreparedCommon :=
  CuSavingsRetainedClaimBindingPrepared.binding isNew CuSavingsRetainedClaimBindingSelector.select common

theorem prepared_equivalence {H : Type} (common : PreparedCommon)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (initial : Array aspis_core.field.WideExact 29#usize) :
    (letI : PreparedCommon := binding true common
     gamma_new.Prepared.gamma_new_new D sem v hash initial)=
    (letI : PreparedCommon := binding false common
     gamma_new.Prepared.gamma_new_new D sem v hash initial) :=
  CuSavingsRetainedClaimBindingPrepared.prepared_equivalence common CuSavingsRetainedClaimBindingSelector.select D sem v hash initial

variable [RetainedPrefix]
theorem tx1_prepare_equivalence {H : Type} (common : PreparedCommon)
    (D : aspis_core.Digest32 H) (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase→Result Unit))
    (initial : Array aspis_core.field.WideExact 29#usize) :
    (letI : PreparedCommon := binding true common
     retained.tx1_prepare D publicValue v hash obs initial)=
    (letI : PreparedCommon := binding false common
     retained.tx1_prepare D publicValue v hash obs initial) := by
  have hprep : @gamma_new.Prepared.gamma_new_new (binding true common) _ =
      @gamma_new.Prepared.gamma_new_new (binding false common) _ := by
    funext H D sem v hash initial
    exact prepared_equivalence common D sem v hash initial
  unfold retained.tx1_prepare
  rw [hprep]

#print axioms prepared_equivalence
#print axioms tx1_prepare_equivalence
end AspisR1.CuSavingsRetainedClaimBindingFinal
