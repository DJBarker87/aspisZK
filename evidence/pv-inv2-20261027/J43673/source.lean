import R1Z.PV_Inv_WordTuple
set_option autoImplicit false
namespace R1Z.PV_Inv_TagWord
open Aeneas Aeneas.Std
open ProverCommitScalar48 (embed)
open AspisR1.ExtractedCurrentQM31Exact (QM31Exact)

theorem embed_nat (tag : U32) : embed tag = (tag.val : QM31Exact) := rfl

theorem source_tag (tag : U32) (modelTag : Nat) (tag_join : tag.val=modelTag) :
    embed tag = (modelTag : QM31Exact) := by rw [embed_nat,tag_join]

#print axioms embed_nat
#print axioms source_tag
end R1Z.PV_Inv_TagWord
