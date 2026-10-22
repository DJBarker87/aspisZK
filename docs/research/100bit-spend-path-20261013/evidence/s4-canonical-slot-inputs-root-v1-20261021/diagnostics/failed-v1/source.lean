import S4CanonicalQmWordRootV1
import S4CanonicalHeadInputsRootV1
import S4FourCallbacksForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCanonicalSlotInputsRootV1
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (canonical slice)
open AspisR1FastDotsCanonicalQmWordRootV1 (canonical_slice canonical_qm_parser_forward)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsCurrentQmParserRootV1 (QM parser)
open AspisR1FastDotsFirstTailReadTotalRootV1 (FirstReadWitness first_tail_reads_total)
open AspisR1FastDotsTailReadTotalRootV1 (ReadWitness tail_reads_total)

theorem canonical_read16_parser_forward (a : Array Std.U8 608#usize)
    (bytes : Slice Std.U8) (offset : Nat)
    (hc : canonical (bytesOf a.val))
    (hbytes : bytes.val=a.val.slice offset (offset+16))
    (hlen : bytes.val.length=16) (halign : offset%4=0) (hbound : offset+16≤608) :
    ∃ q : QM, parser bytes=.ok (some q) := by
  have hsub : canonical (slice (bytesOf a.val) offset 16) :=
    canonical_slice (bytesOf a.val) offset 16 hc halign (by decide)
      (by simpa only [bytesOf,List.length_map,a.property] using hbound)
  have he : bytesOf bytes.val=slice (bytesOf a.val) offset 16 := by
    simp only [bytesOf,hbytes,List.slice,slice,List.map_take,List.map_drop,Nat.add_sub_cancel_left]
  have hcan : canonical (bytesOf bytes.val) := by rw [he]; exact hsub
  let fixed : Array Std.U8 16#usize := ⟨bytes.val,hlen⟩
  obtain ⟨q,hq⟩ := canonical_qm_parser_forward fixed hcan
  have heq : Array.to_slice fixed=bytes := Subtype.ext rfl
  rw [heq] at hq
  exact ⟨q,hq⟩

theorem canonical_first_tail_parser (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (r : FirstReadWitness a g slot)
    (hs : slot.val<4) (hc : canonical (bytesOf a.val)) :
    ∃ q : QM, parser r.bytes=.ok (some q) := by
  apply canonical_read16_parser_forward a r.bytes (slot.val*120+104) hc
  · simpa only [Nat.add_assoc] using
      (r.bytes_value.trans (by rw [r.start_value,r.finish_value]))
  · exact r.bytes_length
  · simp [Nat.add_mod,Nat.mul_mod]
  · omega

theorem canonical_tail_parser (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot term : Usize) (r : ReadWitness a g slot term)
    (hs : slot.val<4) (ht : term.val<2) (hc : canonical (bytesOf a.val)) :
    ∃ q : QM, parser r.bytes=.ok (some q) := by
  apply canonical_read16_parser_forward a r.bytes (480+slot.val*32+term.val*16) hc
  · rw [r.bytes_value,r.offset_value,r.finish_value]
  · exact r.bytes_length
  · simp [Nat.add_mod,Nat.mul_mod]
  · omega

/-- One canonical payload supplies all116 source parser acceptances: 26 M31
and3 QM31 values per slot. Exact source read witnesses are constructed. -/
theorem canonical_slot_input (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (hs : slot.val<4) (hc : canonical (bytesOf a.val)) :
    AspisR1FastDotsFourCallbacksForwardRootV1.SlotInput a g slot := by
  constructor
  · exact AspisR1FastDotsCanonicalHeadInputsRootV1.canonical_all_head_parsed_at a g hc slot hs
  · obtain ⟨first⟩ := first_tail_reads_total a g slot hs
    obtain ⟨r0⟩ := tail_reads_total a g slot 0#usize hs (by decide)
    obtain ⟨r1⟩ := tail_reads_total a g slot 1#usize hs (by decide)
    obtain ⟨qfirst,hpf⟩ := canonical_first_tail_parser a g slot first hs hc
    obtain ⟨q0,hp0⟩ := canonical_tail_parser a g slot 0#usize r0 hs (by decide) hc
    obtain ⟨q1,hp1⟩ := canonical_tail_parser a g slot 1#usize r1 hs (by decide) hc
    exact ⟨first,r0,r1,qfirst,q0,q1,hpf,hp0,hp1⟩
#print axioms canonical_read16_parser_forward
#print axioms canonical_first_tail_parser
#print axioms canonical_tail_parser
#print axioms canonical_slot_input
end AspisR1FastDotsCanonicalSlotInputsRootV1
