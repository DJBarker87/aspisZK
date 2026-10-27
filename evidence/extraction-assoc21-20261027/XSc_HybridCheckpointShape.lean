import XSc_HybridMaterialized
import XSc_FinishRestore
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_HybridCheckpointShape
/-- The actual saved-checkpoint cut has64 restored weights and next=10.
Canonical saved-field/model provenance and byte/trace association stay separate. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : XRz_HybridTx1.tx1 XRz_HybridSampler.adopted D pub physical proof split hash obs=ok (.Ok saved)) :
 ∃ (p : verifier.Prepared) (a : verifier.Accumulator),
 a.weights.val.length=64 ∧ a.next.val=10 ∧
 verifier.checkpoint D p a proof physical hash=ok saved := by
 obtain ⟨p,g,initial,a,geo,pending0,pending,slice,finished,restore,
  hinit,hnew,hquery,hborrow,hsize,hraw,hnext,hfinish,heq,hcheckpoint⟩ :=
  XSc_HybridMaterialized.source D pub physical proof split hash obs saved run
 have frame := XSc_FinishRestore.source a pending slice finished restore hborrow (by change slice.val.length≤pending.raw.val.length;omega) hfinish
 have splitEq := (XRz_HybridCuts.source XRz_HybridSampler.adopted D pub physical proof split hash obs saved run).1
 have savedSize : (restore finished).val.length=64 := by rw [frame.1,frame.2,hsize]
 refine ⟨p,{a with weights:=restore finished},savedSize,?_,hcheckpoint⟩
 change a.next.val=10
 rw [hnext,splitEq]
 unfold compact.SPLIT
 rfl
#print axioms source
end XSc_HybridCheckpointShape
