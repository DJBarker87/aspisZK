import R1Z.ProverRwQueryMembership

/-! Finite control refinement of the actual ordered 64-word query owner.
All byte reads, errors, duplicate handling, array updates and selected advance
states are retained; no dictionary contract or successful-read premise. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryScan
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Queries := ProverRwQueryContains.Queries
abbrev Blocks := Array (Array U8 32#usize) 8#usize
abbrev Output := core.result.Result (Queries × Array U8 32#usize) verifier.Error

def dispatch
  (recur : Queries → Usize → Usize → Result Output)
  (blocks : Array (Array Std.U8 32#usize) 8#usize)
  (advances : Array (Array Std.U8 32#usize) 8#usize)
  (accepted : Array Std.U32 22#usize) (n : Std.Usize) (draws : Std.Usize) :
  Result (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8
    32#usize)) verifier.Error)
  := do
  if draws = 64#usize
  then
    if n = 22#usize
    then
      let a ← Array.index_usize advances 7#usize
      ok (core.result.Result.Ok (accepted, a))
    else ok (core.result.Result.Err verifier.Error.Transcript)
  else
    let k ← draws / 8#usize
    if n = 22#usize
    then
      let a ← Array.index_usize advances k
      ok (core.result.Result.Ok (accepted, a))
    else
      let i ← draws % 8#usize
      let at1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i)
      let a ← Array.index_usize blocks k
      let i1 ← Array.index_usize a at1
      let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize)
      let i3 ← Array.index_usize a i2
      let i4 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize)
      let i5 ← Array.index_usize a i4
      let i6 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize)
      let i7 ← Array.index_usize a i6
      let i8 ←
        Aeneas.Std.lift (core.num.U32.from_le_bytes
          (Array.make 4#usize [ i1, i3, i5, i7 ]))
      let candidate ← Aeneas.Std.lift (i8 &&& 262143#u32)
      let b ← host_transcript.query_contains accepted n candidate
      if b
      then
        let i9 ← Aeneas.Std.lift (Std.Usize.wrapping_add draws 1#usize)
        recur accepted n i9
      else
        let accepted1 ← Array.update accepted n candidate
        let i9 ← Aeneas.Std.lift (Std.Usize.wrapping_add n 1#usize)
        let i10 ← Aeneas.Std.lift (Std.Usize.wrapping_add draws 1#usize)
        recur accepted1 i9 i10

theorem source_unfold (blocks advances : Blocks) (accepted : Queries) (n draws : Usize) :
    host_transcript.scan_query_words blocks advances accepted n draws =
      dispatch (host_transcript.scan_query_words blocks advances) blocks advances accepted n draws := by
  rw [host_transcript.scan_query_words]
  rfl

theorem dispatch_congr (blocks advances : Blocks) (accepted : Queries) (n draws : Usize)
    (left right : Queries → Usize → Usize → Result Output)
    (same : ∀ a m, left a m (Usize.wrapping_add draws 1#usize) =
      right a m (Usize.wrapping_add draws 1#usize)) :
    dispatch left blocks advances accepted n draws =
      dispatch right blocks advances accepted n draws := by
  unfold dispatch
  split
  · rfl
  · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro k hk
    split
    · rfl
    · repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
      split
      · apply same
      · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro updated hu
        simp only [lift,bind_tc_ok]
        apply same

def finite (blocks advances : Blocks) : Nat → Queries → Usize → Usize → Result Output
  | 0,accepted,n,draws => dispatch (fun _ _ _ => .div) blocks advances accepted n draws
  | fuel+1,accepted,n,draws => dispatch (finite blocks advances fuel) blocks advances accepted n draws

theorem scan_finite (blocks advances : Blocks) (fuel : Nat) (accepted : Queries)
    (n draws : Usize) (bound : draws.val+fuel=64) :
    host_transcript.scan_query_words blocks advances accepted n draws =
      finite blocks advances fuel accepted n draws := by
  induction fuel generalizing accepted n draws with
  | zero =>
    have cap : draws = 64#usize := by apply UScalar.eq_of_val_eq; change draws.val=64; omega
    rw [source_unfold]
    simp only [finite,dispatch,cap,if_true]
  | succ fuel ih =>
    rw [source_unfold]
    change dispatch _ _ _ _ _ _ = dispatch _ _ _ _ _ _
    apply dispatch_congr
    intro a m
    apply ih
    have add : (Usize.wrapping_add draws 1#usize).val = draws.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      have one : (1#usize).val = 1 := rfl
      rw [one,Nat.mod_eq_of_lt]
      have big := (64#usize).hSize
      change 64 < UScalar.size .Usize at big
      omega
    omega

theorem queries_finite (blocks advances : Blocks) :
    host_transcript.queries_from_pairs blocks advances =
      finite blocks advances 64 (Array.repeat 22#usize 0#u32) 0#usize 0#usize := by
  exact scan_finite blocks advances 64 _ _ _ (by rfl)

#print axioms source_unfold
#print axioms dispatch_congr
#print axioms scan_finite
#print axioms queries_finite
end R1Z.ProverRwQueryScan
