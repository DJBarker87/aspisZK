set -e
python3 -B - <<'P'
src=open('inputs/L012_orig.lean').read()
head=src[:src.index('set_option maxHeartbeats 200000 in')]
bs=', '.join(f'b{i}' for i in range(32))
def lm(i): return f'(core.num.U32.from_le_bytes (Array.make 4#usize [b{4*i}, b{4*i+1}, b{4*i+2}, b{4*i+3}]))'
lms=[lm(i) for i in range(8)]
def casc(P):
    s='ok (some { c0 := { c0 := { a := %s, b := %s }, c1 := { a := %s, b := %s } }, c1 := { c0 := { a := %s, b := %s }, c1 := { a := %s, b := %s } } })'%tuple(lms)
    for i in range(7,-1,-1):
        s=f'if {lms[i]} >= {P} then ok none else {s}'
    return s
FP='AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.P'
GP='AspisR1CandidateParser.field.P'
F='AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes'
G='AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes'
body=f'''
open Aeneas Aeneas.Std Result ControlFlow Error
section
variable ({bs} : Std.U8) (hl : [{bs}].length ≤ Usize.max)

example : {FP} = {GP} := by with_unfolding_all rfl

example : {F} ⟨[{bs}], hl⟩ = ({casc(FP)} : Result (Option AspisR1CandidateParser.field.wide_exact.WideExact)) := by
  with_unfolding_all rfl

example : {G} ⟨[{bs}], hl⟩ = ({casc(GP)} : Result (Option AspisR1CandidateParser.field.wide_exact.WideExact)) := by
  with_unfolding_all rfl
end
'''
open('PRVEq_PCVHs2.lean','w').write(head+body)
P
