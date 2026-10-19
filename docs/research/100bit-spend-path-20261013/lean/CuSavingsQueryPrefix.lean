import CuSavingsQueryAccess
import CuSavingsPrefix

/-! Consume the prefix bound from the actual query accessor. The decoder is
arbitrary, so both success and rejection on each observed byte range agree.
The four-dot loop/context source correspondence remains a separate consumer.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsQueryPrefix
open Aeneas Aeneas.Std Result AspisR1CuQuery

theorem decode_range_eq {A : Type} (view : verifier.View) (index : Usize)
    (start finish : Nat) (hf : finish ≤ 608) (decode : List U8 → Result A) :
    (do
      let q ← verifier.View.query view index
      let fixed ← AspisR1CuPrefix.fixed_prefix q
      decode (fixed.val.slice start finish)) = (do
      let q ← verifier.View.query view index
      decode (q.val.slice start finish)) := by
  cases hq : verifier.View.query view index with
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok q =>
    have hb := CuSavingsQueryAccess.query_prefix_bound view index q hq
    simp only [bind_tc_ok,CuSavingsPrefix.source_success q hb,
      CuSavingsPrefix.range_eq q hb start finish hf]

theorem base_decode_eq {A : Type} (view : verifier.View) (index : Usize)
    (slot term : Nat) (hs : slot < 4) (ht : term < 26) (decode : List U8 → Result A) :
    (do
      let q ← verifier.View.query view index
      let fixed ← AspisR1CuPrefix.fixed_prefix q
      decode (fixed.val.slice (slot*120+term*4) (slot*120+term*4+4))) = (do
      let q ← verifier.View.query view index
      decode (q.val.slice (slot*120+term*4) (slot*120+term*4+4))) :=
  decode_range_eq view index _ _ (CuSavingsPrefix.base_range slot term hs ht).2 decode

theorem middle_decode_eq {A : Type} (view : verifier.View) (index : Usize)
    (slot : Nat) (hs : slot < 4) (decode : List U8 → Result A) :
    (do
      let q ← verifier.View.query view index
      let fixed ← AspisR1CuPrefix.fixed_prefix q
      decode (fixed.val.slice (slot*120+104) (slot*120+120))) = (do
      let q ← verifier.View.query view index
      decode (q.val.slice (slot*120+104) (slot*120+120))) :=
  decode_range_eq view index _ _ (CuSavingsPrefix.middle_range slot hs).2 decode

theorem tail_decode_eq {A : Type} (view : verifier.View) (index : Usize)
    (slot term : Nat) (hs : slot < 4) (ht : term < 2) (decode : List U8 → Result A) :
    (do
      let q ← verifier.View.query view index
      let fixed ← AspisR1CuPrefix.fixed_prefix q
      decode (fixed.val.slice (480+slot*32+term*16) (480+slot*32+term*16+16))) = (do
      let q ← verifier.View.query view index
      decode (q.val.slice (480+slot*32+term*16) (480+slot*32+term*16+16))) :=
  decode_range_eq view index _ _ (CuSavingsPrefix.tail_range slot term hs ht).2 decode

#print axioms decode_range_eq
#print axioms base_decode_eq
#print axioms middle_decode_eq
#print axioms tail_decode_eq
end AspisR1.CuSavingsQueryPrefix
