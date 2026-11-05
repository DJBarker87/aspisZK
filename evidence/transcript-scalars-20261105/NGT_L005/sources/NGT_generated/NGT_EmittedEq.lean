import NGT_Emitted
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_EmittedEq
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem absorb {H : Type} (D : aspis_core.Digest32 H)
 (t : transcript.Transcript H) (row : U8) (payload : Slice U8) :
 NGT_Emitted.absorb D t row payload=transcript.Transcript.absorb D t row payload := rfl

theorem block {H : Type} (D : aspis_core.Digest32 H)
 (t : transcript.Transcript H) (row : U8) (payload : Slice U8) :
 NGT_Emitted.block D t row payload=transcript.Transcript.block D t row payload := rfl

theorem scalar (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (t : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
 NGT_Emitted.scalar B D t row payload nonzero=PreparedModel.scalar B D t row payload nonzero := rfl

theorem scalar_k (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (t : transcript.Transcript H) (row : U8) (payload : Slice U8) :
 NGT_Emitted.scalar_k B D t row payload=PreparedModel.scalar_k B D t row payload := rfl
#print axioms absorb
#print axioms block
#print axioms scalar
#print axioms scalar_k
end AspisR1.NGT_EmittedEq
