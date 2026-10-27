import R1Z.PV_Inv_NativeCompress
set_option autoImplicit false
namespace R1Z.PV_Inv_EmbedTag
open Aeneas Aeneas.Std
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)

def liftWord (tag : U32) : Old.Q := ⟨⟨tag,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem canonical (tag : U32) (h : tag.val < AspisCircleGroupOrder.P) : Canonical (liftWord tag) :=
  ⟨⟨h,by change (0#u32).val < AspisCircleGroupOrder.P; decide⟩,⟨by change (0#u32).val < AspisCircleGroupOrder.P; decide,by change (0#u32).val < AspisCircleGroupOrder.P; decide⟩⟩

theorem value (tag : U32) : decode (liftWord tag)=ProverCommitScalar48.embed tag := rfl

#print axioms canonical
#print axioms value
end R1Z.PV_Inv_EmbedTag
