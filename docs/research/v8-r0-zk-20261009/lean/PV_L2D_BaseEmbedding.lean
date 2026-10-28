import PV_L2D_Qm31Embedding
set_option autoImplicit false
namespace PV_L2D_BaseEmbedding
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 PV_L2D_Qm31Embedding

theorem word_zero :
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () 0#u32 = ok 0#u32 := by
  simp only [field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,field.P]
  rfl
#print axioms word_zero

def base (x : U32) : field.QM31 := ⟨⟨x,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem canonical_base (x : U32) : ∃ y,
    field.wide_exact.canonical_qm31 (base x) = ok (base y) := by
  obtain ⟨y,hy⟩ := word_total x
  exact ⟨y,by simp only [field.wide_exact.canonical_qm31,base,hy,word_zero,bind_tc_ok]⟩
#print axioms canonical_base

theorem embed_base (x : U32) : ∃ y,
    field.wide_exact.WideExact.from_qm31 (base x) = ok ⟨base y,field.QM31.ZERO⟩ := by
  obtain ⟨y,hy⟩ := canonical_base x
  exact ⟨y,by simp only [field.wide_exact.WideExact.from_qm31,hy,bind_tc_ok]⟩
#print axioms embed_base

theorem lower_zero_tail (x : U32) (out : field.wide_exact.WideExact)
    (h : field.wide_exact.WideExact.from_qm31 (base x) = ok out) :
    (limbs out).drop 1=List.replicate 7 0 := by
  obtain ⟨y,hy⟩ := embed_base x
  rw [hy] at h
  cases h
  simp only [limbs,base,field.QM31.ZERO,List.drop_succ_cons,List.drop_zero]
  rfl
#print axioms lower_zero_tail
end PV_L2D_BaseEmbedding
