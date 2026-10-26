import F3S_BatchLoop
import Port9OR_BatchTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_BatchTree
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)
 theorem dictionary (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    Port9OR_BatchTree.code base D hash proof queries root batch tree idx val=
      Port9OR_BatchTree.code base E hash proof queries root batch tree idx val := by
  unfold Port9OR_BatchTree.code
  congr 1
  funext raw
  congr 1
  funext keys
  rw [F3S_BatchLoop.dictionary base D E]
#print axioms dictionary
end AspisR1.F3S_BatchTree
end
