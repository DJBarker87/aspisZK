import AspisR1SimSemantic20.Funs
/-! The immutable byte operations reuse the parser cone's slice and clone
proofs (MultiproofConeSlices / MultiproofConeVecLaws), specialized to env J. -/
set_option autoImplicit false
namespace R1Z.ProverCommitFields20
open Aeneas Aeneas.Std Result AspisR1SimSemantic20
abbrev Bytes := alloc.vec.Vec U8

theorem clone_bytes (s : Slice U8) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok s := by
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (by intros;rfl))
  exact ho.trans (congrArg (fun v : alloc.vec.Vec U8 => Result.ok v) hv.symm)

theorem drop_total (bytes : Bytes) (bound : 32≤bytes.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes {start:=32#usize} = ok (Slice.drop bytes 32#usize) := by
  change core.slice.index.Slice.index _ bytes _ = _
  simp only [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    show (32#usize).val≤bytes.length from bound,if_true]

def finite (row : U8) (payload : Bytes) (value : Usize) : Nat →
    Result (core.result.Result Unit r1_wire.Error)
  | 0 => ok (core.result.Result.Ok ())
  | n+1 => do
    if alloc.vec.Vec.len payload < 32#usize then ok (core.result.Result.Ok ())
    else
      let bytes ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        payload {«end»:=32#usize}
      let parsed ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
      match parsed with
      | none => ok (core.result.Result.Err (r1_wire.Error.NonCanonical row value))
      | some x => do
        let q ← aspis_core.field.wide_exact.WideExact.impl.c1 x
        let bad ← core.cmp.PartialEq.ne.trait_default
          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q aspis_core.field.QM31.ZERO
        if bad then ok (core.result.Result.Err (r1_wire.Error.NonCanonical row value))
        else do
          let suffix ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
            payload {start:=32#usize}
          let tail ← alloc.slice.Slice.to_vec core.clone.CloneU8 suffix
          finite row tail (Usize.wrapping_add value 1#usize) n

/-- Complete validator recursion for every finite payload, with exact first
failing field index, ignored short suffix, and errors/divergence of callees. -/
theorem extracted_finite (remaining : Nat) (row : U8) (payload : Bytes) (value : Usize)
    (bound : payload.val.length<32*(remaining+1)) :
    r1_wire.fields20.validate row payload value = finite row payload value remaining := by
  induction remaining generalizing payload value with
  | zero =>
    have short : alloc.vec.Vec.len payload < 32#usize := by change payload.val.length<32;omega
    rw [r1_wire.fields20.validate]
    simp only [short,if_true,finite]
  | succ n ih =>
    rw [r1_wire.fields20.validate]
    simp only [finite]
    by_cases short : alloc.vec.Vec.len payload < 32#usize
    · simp only [short,if_true]
    · simp only [short,if_false]
      have long : 32≤payload.val.length := by change ¬payload.val.length<32 at short;omega
      have tailEq := drop_total payload long
      have tailBound : (Slice.drop payload 32#usize).val.length<32*(n+1) := by
        simp only [Slice.getElem!_val_drop,List.length_drop]
        change payload.val.length-32<32*(n+1)
        omega
      have tailRec := ih (Slice.drop payload 32#usize) (Usize.wrapping_add value 1#usize) tailBound
      cases hp : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
          payload {«end»:=32#usize} with
      | fail e => simp only [bind_tc_fail]
      | div => simp only [bind_tc_div]
      | ok bytes =>
        simp only [bind_tc_ok]
        cases hd : aspis_core.field.wide_exact.WideExact.from_le_bytes bytes with
        | fail e => simp only [bind_tc_fail]
        | div => simp only [bind_tc_div]
        | ok parsed =>
          simp only [bind_tc_ok]
          cases parsed with
          | none => rfl
          | some x =>
            simp only
            cases hc : aspis_core.field.wide_exact.WideExact.impl.c1 x with
            | fail e => simp only [bind_tc_fail]
            | div => simp only [bind_tc_div]
            | ok q =>
              simp only [bind_tc_ok]
              cases he : core.cmp.PartialEq.ne.trait_default
                aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q aspis_core.field.QM31.ZERO with
              | fail e => simp only [bind_tc_fail]
              | div => simp only [bind_tc_div]
              | ok bad =>
                simp only [bind_tc_ok]
                cases bad with
                | true => rfl
                | false =>
                  simp only [Bool.false_eq_true,if_false,tailEq,bind_tc_ok,clone_bytes,lift]
                  exact tailRec

#print axioms clone_bytes
#print axioms drop_total
#print axioms extracted_finite
end R1Z.ProverCommitFields20
