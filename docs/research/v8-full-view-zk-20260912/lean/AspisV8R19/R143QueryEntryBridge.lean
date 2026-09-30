import AspisR137Q22.Funs

/-! Fixed source query entry and bounded wrapping arithmetic.
The inner and outer loops stay symbolic here; full sampler execution is separate. -/
set_option autoImplicit false
namespace AspisV8R19.R143QueryEntryBridge

open Aeneas Aeneas.Std Result

abbrev Values := alloc.vec.Vec U32

def finishSource (out : Values) :
    core.result.Result Values AspisR137Q22.transcript.QuerySampleError :=
  if alloc.vec.Vec.len out = 22#usize then .Ok out
  else .Err (.DrawLimitExhausted (alloc.vec.Vec.len out) 64#usize)

def small64 (n : Nat) (h : n ≤ 64) : Usize :=
  UScalar.ofNatCore n (by have := Usize.cMax_bound; scalar_tac)

theorem small64_val (n : Nat) (h : n ≤ 64) : (small64 n h).val = n := rfl

theorem try_small64 (n : Nat) (h : n ≤ 64) :
    UScalar.tryMk .Usize n = .ok (small64 n h) := by
  have hb : UScalar.inBounds .Usize n := by
    have := Usize.cMax_bound
    scalar_tac
  have hs := UScalar.tryMk_eq .Usize n
  cases he : UScalar.tryMk .Usize n with
  | fail e => simp only [he] at hs; exact False.elim (hs hb)
  | div => simp only [he] at hs
  | ok a =>
      simp only [he] at hs
      congr 1
      apply UScalar.eq_of_val_eq
      exact hs.1

theorem bounded_draw_increment (draws : Usize) (h : draws.val < 64) :
    (draws + 1#usize : Result Usize) =
      .ok (Std.Usize.wrapping_add draws 1#usize) := by
  have hsmall : draws.val + 1 ≤ 64 := by omega
  have htry : (draws + 1#usize : Result Usize) =
      .ok (small64 (draws.val + 1) hsmall) := by
    change UScalar.tryMk .Usize (draws.val + 1) = _
    exact try_small64 _ _
  rw [htry]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [small64_val, Std.Usize.wrapping_add_val_eq, UScalar.size]
  have hlt : draws.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
    have hbound : draws.val + 1 ≤ UScalar.cMax .Usize := by
      have := Usize.cMax_bound
      scalar_tac
    exact UScalar.bound_suffices .Usize (draws.val + 1) hbound
  have h1 : (1#usize : Usize).val = 1 := rfl
  rw [h1, Nat.mod_eq_of_lt hlt]

theorem wrapping_bound :
    Std.U32.wrapping_shl 1#u32 18#u32 = 262144#u32 := by rfl

theorem checked_bound :
    (1#u32 <<< 18#i32 : Result U32) = .ok 262144#u32 := by rfl

theorem wrapping_mask :
    Std.U32.wrapping_sub 262144#u32 1#u32 = 262143#u32 := by rfl

theorem cast_bound : UScalar.cast .Usize 262144#u32 = 262144#usize := by
  apply UScalar.eq_of_val_eq
  simp

theorem selected_entry (self : AspisR137Q22.transcript.Transcript) :
    AspisR137Q22.r137_query_probe self = (do
      let (next, out) ←
        AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0
          self 22#usize 64#usize 262143#u32
          (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize
      ok (finishSource out, next)) := by
  rw [AspisR137Q22.r137_query_probe, wrapping_bound]
  simp only [lift, bind_tc_ok]
  rw [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement]
  simp [wrapping_mask, lift, bind_tc_ok, cast_bound, finishSource]
  intro next out hloop
  split_ifs <;> rfl

#print axioms small64_val
#print axioms try_small64
#print axioms bounded_draw_increment
#print axioms wrapping_bound
#print axioms checked_bound
#print axioms wrapping_mask
#print axioms cast_bound
#print axioms selected_entry
#print axioms AspisR137Q22.r137_query_probe
#print axioms AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement

end AspisV8R19.R143QueryEntryBridge
