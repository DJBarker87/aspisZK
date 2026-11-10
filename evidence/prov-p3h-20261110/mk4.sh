set -e
python3 -B - <<'P'
src=open('inputs/L012_orig.lean').read()
head=src[:src.index('set_option maxHeartbeats 200000 in')]
bs=' '.join(f'b{i}' for i in range(32)); bl=', '.join(f'b{i}' for i in range(32))
FP='AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.P'
GP='AspisR1CandidateParser.field.P'
F='AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes'
G='AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes'
lms=[f'(core.num.U32.from_le_bytes (Array.make 4#usize [b{4*i}, b{4*i+1}, b{4*i+2}, b{4*i+3}]))' for i in range(8)]
def casc(P):
    s='ok (some { c0 := { c0 := { a := %s, b := %s }, c1 := { a := %s, b := %s } }, c1 := { c0 := { a := %s, b := %s }, c1 := { a := %s, b := %s } } })'%tuple(lms)
    for i in range(7,-1,-1):
        s=f'if {lms[i]} >= {P} then ok none else {s}'
    return s
W='(Result (Option AspisR1CandidateParser.field.wide_exact.WideExact))'
defs='AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes, AspisR1CandidateParser.field.QM31.from_le_bytes, AspisR1CandidateParser.field.CM31.from_le_bytes, AspisR1CandidateParser.field.M31.from_le_bytes, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, Aeneas.Std.lift, AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch'
body=f'''
open Aeneas Aeneas.Std Result ControlFlow Error
section
variable ({bs} : Std.U8) (hl : [{bl}].length ≤ Usize.max)
example : {FP} = {GP} := by with_unfolding_all rfl
example : {F} ⟨[{bl}], hl⟩ = ({casc(FP)} : {W}) := by with_unfolding_all rfl
example : {G} ⟨[{bl}], hl⟩ = ({casc(GP)} : {W}) := by
  simp [Slice.len, {defs}]
  trace_state
  sorry
end
'''
open('PRVEq_PCVHs4.lean','w').write(head+body)
P
