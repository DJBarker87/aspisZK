import JFw_Blocks
import JFw_Validator
set_option autoImplicit false
namespace AspisR1.JFw_Chunks
open Aeneas Aeneas.Std Result
open AspisR1RecordParser

theorem split (chunks : List (List U8)) (lengths : ∀ c ∈ chunks,c.length=32) :
    List.toChunksExact 32 (by decide) chunks.flatten = (chunks,[]) := by
  induction chunks with
  | nil => rw [List.flatten_nil,List.toChunksExact];rfl
  | cons c cs ih =>
    have length := lengths c (List.mem_cons_self ..)
    have rest := ih (fun x hx => lengths x (List.mem_cons_of_mem _ hx))
    rw [List.flatten_cons,List.toChunksExact]
    have enough : ¬(c ++ cs.flatten).length < 32 := by
      rw [List.length_append,length];omega
    have take : c.take 32 = c := by simpa only [length] using List.take_length c
    have drop : c.drop 32 = [] := by simpa only [length] using List.drop_length c
    simp only [dif_neg enough,List.take_append,List.drop_append,length,
      Nat.sub_self,List.take_zero,List.append_nil,List.drop_zero,take,drop,
      List.nil_append,rest]


/-- Forward actual validator success from raw block facts, preserving its actual iterator. -/
theorem validator (payload : Slice U8) (chunks : List (List U8)) (row : U8)
    (same : payload.val = chunks.flatten) (count : chunks.length ≤ Usize.max)
    (valid : ∀ c ∈ chunks,c.length=32 ∧ OraclePortCompactDraft.canonical (MultiproofConeCanonical.bytesOf c) ∧
      c.drop 16 = List.replicate 16 0#u8) :
    r1_wire.validate_record_fields row payload = ok (.Ok ()) := by
  have division := split chunks (fun c hc => (valid c hc).1)
  have actual : List.toChunksExact (32#usize).val (by decide) payload.val = (chunks,[]) := by
    rw [same]
    exact division
  unfold r1_wire.validate_record_fields core.slice.Slice.chunks_exact
  simp only [show 0 < (32#usize).val by decide,_root_.dite_true,actual,bind_tc_ok,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  apply JFw_Validator.loop_valid
  · change 0+chunks.attach.length ≤ Usize.max
    simpa only [List.length_attach,Nat.zero_add] using count
  · intro chunk mem
    simp only [List.mem_map] at mem
    obtain ⟨c,hc,eq⟩ := mem
    subst chunk
    obtain ⟨length,canon,zero⟩ := valid c.val c.property
    exact JFw_ChunkDecode.valid _ length canon zero

#print axioms split
#print axioms validator
end AspisR1.JFw_Chunks
