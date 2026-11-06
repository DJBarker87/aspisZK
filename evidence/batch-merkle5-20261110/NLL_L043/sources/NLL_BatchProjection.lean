import NKV_FRef
import Port3_BatchStage
set_option autoImplicit false
noncomputable section
namespace NLL_BatchProjection
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1

/-- Isolated source projection over an abstract operation parameter. This
avoids reducing a large concrete child dictionary during kernel equality
checking. The final native wrapper specializes ops to the actual children. -/
theorem source (ops : Port3_NativeBatchBody.Ops) {X : Type}
 (D : aspis_core.digest.Digest32 X) (hash : X) (proof : Slice U8)
 (p : verifier.Prepared) (folded : Array U8 32#usize) (batch : Usize) :
 NKV_FRef.verifier.candidate.batch_merkle ops D proof p folded batch hash=
 NKV_FRef.verifier.candidate.batch_merkle_values ops D proof p.queries (Port3_BatchStage.roots p folded) batch hash := by
 have h0 : Array.index_usize p.roots 0#usize=ok (Port3_BatchStage.root0 p) := by
   simp [Array.index_usize,Port3_BatchStage.root0,List.getElem?_eq_getElem]
 have h1 : Array.index_usize p.roots 1#usize=ok (Port3_BatchStage.root1 p) := by
   simp [Array.index_usize,Port3_BatchStage.root1,List.getElem?_eq_getElem]
 unfold NKV_FRef.verifier.candidate.batch_merkle
 rw [h0]
 simp only [bind_tc_ok]
 rw [h1]
 simp only [bind_tc_ok]
 exact congrArg (fun rs => NKV_FRef.verifier.candidate.batch_merkle_values ops D proof p.queries rs batch hash)
   (show Array.make 3#usize [Port3_BatchStage.root0 p,Port3_BatchStage.root1 p,folded]=Port3_BatchStage.roots p folded from rfl)

set_option pp.proofs false
#print source
#print axioms source
end NLL_BatchProjection
end
