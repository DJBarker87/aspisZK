set -e
python3 -B - <<'P'
src=open('inputs/L012_orig.lean').read()
head=src[:src.index('set_option maxHeartbeats 200000 in')]
bs=' '.join(f'b{i}' for i in range(8)); bl=', '.join(f'b{i}' for i in range(8))
G='AspisR1CandidateParser.field.'
lm=lambda i: f'(core.num.U32.from_le_bytes (Array.make 4#usize [b{4*i}, b{4*i+1}, b{4*i+2}, b{4*i+3}]))'
body=f'''
open Aeneas Aeneas.Std Result ControlFlow Error
section
variable ({bs} : Std.U8) (hl : [{bl}].length ≤ Usize.max)
example : {G}P = AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.P := by with_unfolding_all rfl

-- fresh from_limbs / gate-shape sanity: CM31 level
example : {G}CM31.from_le_bytes ⟨[{bl}], hl⟩ =
  (if {lm(0)} >= {G}P then ok none else if {lm(1)} >= {G}P then ok none else ok (some {{ a := {lm(0)}, b := {lm(1)} }})) := by
  unfold {G}CM31.from_le_bytes
  by_cases hx : {lm(0)} >= {G}P
  · simp [hx, {G}M31.from_le_bytes, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from]
    trace_state
    sorry
  · by_cases hy : {lm(1)} >= {G}P
    · simp [hx, hy, {G}M31.from_le_bytes, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from]
      trace_state
      sorry
    · sorry
end
'''
open('PRVEq_PCVHs3.lean','w').write(head+body)
P
