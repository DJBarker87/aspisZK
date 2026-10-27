import XRk_CheckpointModel
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRl_CheckpointBytes
/-- Physical encoding sizes of the exact supplied checkpoint external model.
Native method-byte correspondence is separate; the Kani leaf packet checks its
four/eight-limb canonical domains. -/
theorem word_length (x : U32) : (XRk_wordBytes x).length=4 := by
  simp only [XRk_wordBytes,List.length_map,List.length_range]

theorem q_length (x : aspis_core.field.QM31) : (XRk_qBytes x).length=16 := by
  simp only [XRk_qBytes,List.flatMap_cons,List.flatMap_nil,List.length_append,word_length,List.length_nil]

theorem wide_total (x : XRk_Wide) :
    ∃ out, aspis_core.field.wide_exact.WideExact.to_le_bytes x=ok out ∧
      out.val=XRk_qBytes (newQ x.c0)++XRk_qBytes (newQ x.c1) := by
  have size : (XRk_qBytes (newQ x.c0)++XRk_qBytes (newQ x.c1)).length=32 := by
    rw [List.length_append,q_length,q_length]
  unfold aspis_core.field.wide_exact.WideExact.to_le_bytes
  rw [dif_pos size]
  exact ⟨_,rfl,rfl⟩
#print axioms word_length
#print axioms q_length
#print axioms wide_total
end XRl_CheckpointBytes
