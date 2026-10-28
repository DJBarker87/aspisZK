import AspisR1PublicPreparation.Funs
import S1M31EmbeddingSourceV1
set_option autoImplicit false
noncomputable section
namespace NBG_Constructors
open Aeneas Aeneas.Std Result

theorem cm31_new (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b =
      ok (⟨a,b⟩ : AspisR1PublicPreparation.aspis_core.field.CM31) := rfl

theorem qm31_from_cm31 (x : AspisS1M31Embedding.aspis_core.field.CM31) :
    AspisS1M31Embedding.aspis_core.field.QM31.from_cm31 x =
      ok (⟨x,⟨0#u32,0#u32⟩⟩ : AspisS1M31Embedding.aspis_core.field.QM31) := rfl

#print axioms cm31_new
#print axioms qm31_from_cm31
end NBG_Constructors
