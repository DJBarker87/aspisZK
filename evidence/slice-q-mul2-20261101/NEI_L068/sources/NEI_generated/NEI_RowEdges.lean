import NEI_RowBridge
import NEI_PushRawBridge
set_option autoImplicit false
noncomputable section
namespace NEI_RowEdges
open Aeneas Aeneas.Std Result
/-- The actual source helper, SAME carrier/index/word, with no field restriction. -/
theorem residue (row : Array U64 4#usize) (index : Usize) (bound : index.val<4) :
 ∃ out, NEG_RowIsolated.residue_limb_at row index=ok out ∧
 out=row.val[index.val]'(by rw [row.property];exact bound) := by
 obtain ⟨out,limb,run,_,value,_⟩ := NEG_RowStepAssociation.reads row (Array.repeat 4#usize 0#u32) index bound
 exact ⟨out,run,value⟩

theorem power (limbs : Array U32 4#usize) (index : Usize) (bound : index.val<4) :
 ∃ out, NEG_RowIsolated.power_limb_at limbs index=ok out ∧
 out=limbs.val[index.val]'(by rw [limbs.property];exact bound) := by
 obtain ⟨old,out,_,run,_,value⟩ := NEG_RowStepAssociation.reads (Array.repeat 4#usize 0#u64) limbs index bound
 exact ⟨out,run,value⟩

/-- Every reached native/source loop index establishes both helper domains. -/
theorem index_domain (iter : core.ops.range.Range Usize)
 (active : iter.start.val<iter.end.val) (stop : iter.end=4#usize) : iter.start.val<4 :=
 NEG_RowStepAssociation.reached_index iter active stop

/-- The two actual u32-to-u64 conversions are lossless on the entire carrier. -/
theorem widen (value : U32) :
 (core.convert.num.FromU64U32.from value).val=value.val :=
 ExtractedCurrentCM31Mul.widen_value value
#print axioms residue
#print axioms power
#print axioms index_domain
#print axioms widen
end NEI_RowEdges
end
