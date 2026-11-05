import NIF_FieldDomain
import NIF_QueryEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_DotDomains
open Aeneas Aeneas.Std Result OraclePortCompactDraft MultiproofConeCanonical

theorem main_opening (proof : Slice U8) (size : proof.val.length=57607)
 (scan : OraclePortCompactDraft.scan (bytesOf proof.val)) (i : Usize) (inside : i.val<22) :
 ∃ q, Port4B_Opening.opening proof i=ok q ∧ q.val.length=832 ∧
 canonical ((bytesOf q.val).take 608) := by
 obtain ⟨q,hq,length,same⟩:=Port4B_Opening.opening_exact proof size i inside
 refine ⟨q,hq,length,?_⟩
 rw [same]
 exact (scan.2.2.2 i.val (List.mem_range.mpr inside)).1

theorem scalar_window (q : Slice U8) (length : q.val.length=832)
 (checked : canonical ((bytesOf q.val).take 608))
 (slot term : Nat) (sl : slot<4) (tm : term<26) :
 canonical (slice ((bytesOf q.val).take 608) (slot*120+term*4) 4) := by
 apply NIF_FieldDomain.canonical_window _ checked _ _ (by omega) (by decide)
 simp only [bytesOf,List.length_take,List.length_map,length]
 omega

theorem tail0_window (q : Slice U8) (length : q.val.length=832)
 (checked : canonical ((bytesOf q.val).take 608)) (slot : Nat) (sl : slot<4) :
 canonical (slice ((bytesOf q.val).take 608) (slot*120+104) 16) := by
 apply NIF_FieldDomain.canonical_window _ checked _ _ (by omega) (by decide)
 simp only [bytesOf,List.length_take,List.length_map,length]
 omega

theorem tail_window (q : Slice U8) (length : q.val.length=832)
 (checked : canonical ((bytesOf q.val).take 608)) (slot limb : Nat) (sl : slot<4) (lm : limb<2) :
 canonical (slice ((bytesOf q.val).take 608) (480+slot*32+limb*16) 16) := by
 apply NIF_FieldDomain.canonical_window _ checked _ _ (by omega) (by decide)
 simp only [bytesOf,List.length_take,List.length_map,length]
 omega
#print axioms main_opening
#print axioms scalar_window
#print axioms tail0_window
#print axioms tail_window
end AspisR1.NIF_DotDomains
