import AspisV8R19.R632DecoderBlockArray

set_option autoImplicit false
namespace AspisV8R19.R634DecoderPrefixCanonical

open Aeneas Aeneas.Std
open AspisV8R19.R624DecoderInnerExecution

def prefixCanonical {N : Usize} (out : Array U32 N) (k : Nat) : Prop :=
  ∀ x ∈ out.val.take k, x.val < 2147483647

theorem blockOutput8_prefixCanonical {N : Usize} (block : Usize)
    (v : Array U64 8#usize) (out : Array U32 N)
    (hblock : 8 * (block.val + 1) ≤ N.val)
    (hprefix : prefixCanonical out (8 * block.val))
    (hwords : ∀ x ∈ blockWords v, x.val < 2147483647) :
    prefixCanonical (blockOutput8 block v out) (8 * (block.val + 1)) := by
  let off := 8 * block.val
  let fin := 8 * (block.val + 1)
  have hxs : out.val.length = N.val := out.property
  have hoff : off ≤ out.val.length := by dsimp [off]; rw [hxs]; omega
  have hfin : fin = off + 8 := by dsimp [fin, off]; omega
  have hprefixlen : (out.val.take off ++ blockWords v).length = fin := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left hoff]
    have hwlen : (blockWords v).length = 8 := by simp [blockWords]
    rw [hwlen, hfin]
  have htake :
      (out.val.take off ++ blockWords v ++ out.val.drop fin).take fin =
        out.val.take off ++ blockWords v := by
    rw [List.take_append_of_le_length (by rw [hprefixlen]; omega)]
    exact List.take_of_length_le (by rw [hprefixlen])
  intro x hx
  rw [AspisV8R19.R632DecoderBlockArray.blockOutput8_segment block v out hblock] at hx
  change x ∈ (out.val.take off ++ blockWords v ++ out.val.drop fin).take fin at hx
  rw [htake] at hx
  rcases List.mem_append.mp hx with hpre | hword
  · rcases List.mem_iff_getElem.mp hpre with ⟨i, hi, hget⟩
    have hiOff : i < off := by
      have hlen : (out.val.take off).length = off := by
        simp only [List.length_take, Nat.min_eq_left hoff]
      rw [hlen] at hi
      exact hi
    have hgetOut : out.val[i] = x := by simpa using hget
    have hxprefix := hprefix x (List.mem_iff_getElem.mpr ⟨i, hiOff, hgetOut⟩)
    simpa [hgetOut] using hxprefix
  · exact hwords x hword

theorem fullPrefixCanonical_all {N : Usize} (out : Array U32 N)
    (h : prefixCanonical out N.val) :
    ∀ x ∈ out.val, x.val < 2147483647 := by
  intro x hx
  have htake : out.val.take N.val = out.val :=
    List.take_of_length_le (by rw [out.property])
  exact h x (by simpa [htake] using hx)

#print axioms prefixCanonical
#print axioms blockOutput8_prefixCanonical
#print axioms fullPrefixCanonical_all

end AspisV8R19.R634DecoderPrefixCanonical
