import NIH_RawReduce
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_RawExtension

theorem result (limbs : Array U64 4#usize) :
 ∃ a b c d : U32,
 FIq_Native.state_only_poseidon.extension_from_raw_limbs limbs=
   ok ⟨⟨a,b⟩,⟨c,d⟩⟩ ∧
 a.val=(limbs.val[0]'(by have h:=limbs.property;scalar_tac)).val%2147483647 ∧
 b.val=(limbs.val[1]'(by have h:=limbs.property;scalar_tac)).val%2147483647 ∧
 c.val=(limbs.val[2]'(by have h:=limbs.property;scalar_tac)).val%2147483647 ∧
 d.val=(limbs.val[3]'(by have h:=limbs.property;scalar_tac)).val%2147483647 ∧
 a.val<2147483647 ∧ b.val<2147483647 ∧ c.val<2147483647 ∧ d.val<2147483647 := by
 have h0:=ExtractedMaskHornerStep.array_index_usize_ok limbs 0#usize (by decide)
 have h1:=ExtractedMaskHornerStep.array_index_usize_ok limbs 1#usize (by decide)
 have h2:=ExtractedMaskHornerStep.array_index_usize_ok limbs 2#usize (by decide)
 have h3:=ExtractedMaskHornerStep.array_index_usize_ok limbs 3#usize (by decide)
 have v0 : (0#usize).val=0 := by decide
 have v1 : (1#usize).val=1 := by decide
 have v2 : (2#usize).val=2 := by decide
 have v3 : (3#usize).val=3 := by decide
 simp only [v0,v1,v2,v3] at h0 h1 h2 h3
 obtain ⟨a,ra,va,ca⟩:=NIH_RawReduce.result (limbs.val[0]'(by have h:=limbs.property;scalar_tac))
 obtain ⟨b,rb,vb,cb⟩:=NIH_RawReduce.result (limbs.val[1]'(by have h:=limbs.property;scalar_tac))
 obtain ⟨c,rc,vc,cc⟩:=NIH_RawReduce.result (limbs.val[2]'(by have h:=limbs.property;scalar_tac))
 obtain ⟨d,rd,vd,cd⟩:=NIH_RawReduce.result (limbs.val[3]'(by have h:=limbs.property;scalar_tac))
 refine ⟨a,b,c,d,?_,va,vb,vc,vd,ca,cb,cc,cd⟩
 simp only [FIq_Native.state_only_poseidon.extension_from_raw_limbs,h0,h1,h2,h3,
  ra,rb,rc,rd,FIq_Native.field.CM31.new,bind_tc_ok]

#print axioms result
end AspisR1.NIH_RawExtension
