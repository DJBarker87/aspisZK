import NDI_TranscriptRef.Funs
set_option autoImplicit false
namespace NDI_TranscriptWindows
open Aeneas Aeneas.Std Result

theorem initialize (reply : Array U8 32#usize) (j : Usize) (bound : j.val<32) :
    ∃ value, NDI_TranscriptRef.transcript_new_byte_ref reply j=ok (value,0#u8,1#u8) ∧
      reply.val[j.val]?=some value := by
  obtain ⟨value,read,contents⟩ := WP.spec_imp_exists
    (Array.index_usize_spec reply j (by scalar_tac))
  refine ⟨value,?_,?_⟩
  · simp only [NDI_TranscriptRef.transcript_new_byte_ref,read,bind_tc_ok]
  · rw [List.getElem?_eq_getElem (by have := reply.property;scalar_tac),contents]

theorem sample (block advanced : Array U8 32#usize) (row next : U8) (j : Usize)
    (bound : j.val<32) (inc : row+1#u8=ok next) :
    ∃ a b, NDI_TranscriptRef.transcript_sample_byte_ref block advanced row j=ok (a,b,next,3#u8) ∧
      block.val[j.val]?=some a ∧ advanced.val[j.val]?=some b := by
  obtain ⟨a,ha,va⟩ := WP.spec_imp_exists (Array.index_usize_spec block j (by scalar_tac))
  obtain ⟨b,hb,vb⟩ := WP.spec_imp_exists (Array.index_usize_spec advanced j (by scalar_tac))
  refine ⟨a,b,?_,?_,?_⟩
  · simp only [NDI_TranscriptRef.transcript_sample_byte_ref,ha,hb,inc,bind_tc_ok]
  · rw [List.getElem?_eq_getElem (by have := block.property;scalar_tac),va]
  · rw [List.getElem?_eq_getElem (by have := advanced.property;scalar_tac),vb]

theorem complete (a b : Array U8 32#usize)
    (bytes : ∀ j, j<32 → a.val[j]?=b.val[j]?) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro j
  by_cases active : j<32
  · exact bytes j active
  · have sa := a.property
    have sb := b.property
    rw [List.getElem?_eq_none (by scalar_tac),List.getElem?_eq_none (by scalar_tac)]

#print axioms initialize
#print axioms sample
#print axioms complete
end NDI_TranscriptWindows
