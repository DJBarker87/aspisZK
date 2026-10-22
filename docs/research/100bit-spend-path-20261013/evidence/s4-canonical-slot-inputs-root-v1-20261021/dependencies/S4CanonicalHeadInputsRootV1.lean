import S4CanonicalHeadWordRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCanonicalHeadInputsRootV1
open AspisR1FastDotsHeadReadForwardRootV1 (Wide ReadWitness head_reads_total)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt)
open AspisR1FastDotsCanonicalHeadWordRootV1 (current_m31_parser_forward)
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (canonical slice little)

theorem head_read_literal_bytes (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (r : ReadWitness a g slot term) :
    bytesOf r.copied.val=slice (bytesOf a.val) (4*(slot.val*30+term.val)) 4 := by
  have hcopy := r.copied_value.trans r.bytes_value
  rw [r.start_value,r.finish_value] at hcopy
  have hstart : 4*(slot.val*30+term.val)=slot.val*120+term.val*4 := by omega
  simp only [bytesOf,hcopy,List.slice,slice,List.map_take,List.map_drop,
    Nat.add_sub_cancel_left,hstart]

theorem canonical_head_parsed_at
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot term : Usize)
    (hs : slot.val<4) (ht : term.val<26)
    (hc : canonical (bytesOf a.val)) : ParsedAt a g slot term := by
  obtain ⟨r⟩ := head_reads_total a g slot term hs ht
  have hj : slot.val*30+term.val < (bytesOf a.val).length/4 := by
    simp only [bytesOf,List.length_map,a.property]
    change slot.val*30+term.val<152
    omega
  have hword := hc.2 (slot.val*30+term.val) (List.mem_range.mpr hj)
  have hbytes : little (bytesOf r.copied.val)<2147483647 := by
    rw [head_read_literal_bytes a g slot term r]
    exact hword
  exact ⟨r,core.num.U32.from_le_bytes r.copied,current_m31_parser_forward r.copied hbytes⟩

/-- The strict scanner's canonical 608-byte payload supplies every one of
the 26 head parser acceptances for every actual slot. No scalar decoder
success is assumed. Stored-proof/query-prefix identity remains a caller join. -/
theorem canonical_all_head_parsed_at
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hc : canonical (bytesOf a.val)) :
    ∀ slot : Usize, slot.val<4 → ∀ term : Usize, term.val<26 → ParsedAt a g slot term := by
  intro slot hs term ht
  exact canonical_head_parsed_at a g slot term hs ht hc
#print axioms head_read_literal_bytes
#print axioms canonical_head_parsed_at
#print axioms canonical_all_head_parsed_at
end AspisR1FastDotsCanonicalHeadInputsRootV1
