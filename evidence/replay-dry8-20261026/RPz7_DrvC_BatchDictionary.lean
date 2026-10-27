import RPz7_DrvC_SecondFlow
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_BatchDictionary
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port9OR_BatchStep (Indices Values)

theorem loop {H : Type} (base : Port3_NativeBatchBody.Ops)
    (D E : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (root : SdkC_Source.Digest) (tree lo n slot : Usize)
    (keys : Array U64 16#usize) (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos =
      Port9OR_BatchLoop.code base E hash proof root tree lo n slot keys fuel idx val d pos := by
  induction fuel generalizing idx val d pos with
  | zero => rfl
  | succ fuel ih =>
    simp only [Port9OR_BatchLoop.code,Port9OR_BatchLoop.body_dictionary base D E hash]
    apply DrvC_Flow.code_bind_congr
    intro out
    cases out with
    | done result => rfl
    | cont next => exact ih next.1 next.2.1 next.2.2.1 next.2.2.2

theorem tree {H : Type} (base : Port3_NativeBatchBody.Ops)
    (D E : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : SdkC_Source.Digest)
    (batch which : Usize) (idx : Indices) (val : Values) :
    Port9OR_BatchTree.code base D hash proof queries root batch which idx val =
      Port9OR_BatchTree.code base E hash proof queries root batch which idx val := by
  simp only [Port9OR_BatchTree.code,loop base D E hash]

theorem values {H : Type} (base : Port3_NativeBatchBody.Ops)
    (D E : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array SdkC_Source.Digest 3#usize) (batch : Usize) :
    Port9OR_Batch.values base D hash proof queries roots batch =
      Port9OR_Batch.values base E hash proof queries roots batch := by
  simp only [Port9OR_Batch.values,tree base D E hash]

theorem code {H : Type} (D E : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array SdkC_Source.Digest 2#usize) (folded : SdkC_Source.Digest) (batch : Usize) :
    SdkC_BatchSource.code D hash proof queries roots folded batch =
      SdkC_BatchSource.code E hash proof queries roots folded batch := by
  simp only [SdkC_BatchSource.code,values Port4B_Install.leaves D E hash]

#print axioms loop
#print axioms tree
#print axioms values
#print axioms code
end AspisR1.DrvC_BatchDictionary
end
