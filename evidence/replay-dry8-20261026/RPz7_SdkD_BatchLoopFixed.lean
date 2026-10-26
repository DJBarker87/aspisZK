import RPz7_SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_BatchLoopFixed
open Aeneas Aeneas.Std Result
open Port9OR_BatchStep (Indices Values)

theorem loop (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : SdkC_Source.Digest) (tree lo n slot : Usize)
    (keys : Array U64 16#usize) (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos =
      Port9OR_BatchLoop.code base E hash proof root tree lo n slot keys fuel idx val d pos := by
  induction fuel generalizing idx val d pos with
  | zero => rfl
  | succ fuel ih =>
    simp only [Port9OR_BatchLoop.code,Port9OR_BatchLoop.body_dictionary base D E]
    congr 1
    funext out
    cases out with
    | done result => rfl
    | cont next => exact ih next.1 next.2.1 next.2.2.1 next.2.2.2

theorem tree (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : SdkC_Source.Digest)
    (batch kind : Usize) (idx : Indices) (val : Values) :
    Port9OR_BatchTree.code base D hash proof queries root batch kind idx val =
      Port9OR_BatchTree.code base E hash proof queries root batch kind idx val := by
  simp only [Port9OR_BatchTree.code,loop base D E]

#print axioms loop
#print axioms tree
end AspisR1.SdkD_BatchLoopFixed
end
