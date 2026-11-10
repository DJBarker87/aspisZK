set -e
python3 -B - <<'P'
src=open('inputs/L012_orig.lean').read()
head=src[:src.index('set_option maxHeartbeats 200000 in')]
def vs(n): return ' '.join(f'b{i}' for i in range(n))
def ls(n): return ', '.join(f'b{i}' for i in range(n))
def lm(o): return f'(lm b{o} b{o+1} b{o+2} b{o+3})'
xs=' '.join(f'x{i}' for i in range(8))
def casc():
    s='ok (some { c0 := { c0 := { a := x0, b := x1 }, c1 := { a := x2, b := x3 } }, c1 := { c0 := { a := x4, b := x5 }, c1 := { a := x6, b := x7 } } })'
    for i in range(7,-1,-1): s=f'if x{i} >= field.P then ok none else {s}'
    return s
chain_cases=''
# nested by_cases
ind='  '
lines=[]
def gen(i,depth):
    pad='  '*(depth+1)
    if i==8:
        lines.append(pad+'simp [dec_w, dec_qm, dec_cm, '+', '.join(f'h{j}' for j in range(8))+']'); return
    lines.append(pad+f'by_cases h{i} : x{i} >= field.P')
    lines.append(pad+f'· simp [dec_w, dec_qm, dec_cm, '+', '.join(f'h{j}' for j in range(i+1))+']')
    lines.append(pad+'· ')
    # continue in the last bullet: need nested indentation
    lines[-1]=pad+'· '+'rename_i hh'  # placeholder
    gen(i+1,depth+1)
gen(0,0)
chain='\n'.join(lines)
chain_text=f'''
theorem chain ({xs} : Std.U32) :
    (ok (dec_w (dec_qm (dec_cm x0 x1) (dec_cm x2 x3)) (dec_qm (dec_cm x4 x5) (dec_cm x6 x7))) : Result (Option W)) =
    ({casc()} : Result (Option W)) := by
  by_cases h0 : x0 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0]
  by_cases h1 : x1 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1]
  by_cases h2 : x2 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2]
  by_cases h3 : x3 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3]
  by_cases h4 : x4 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4]
  by_cases h5 : x5 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5]
  by_cases h6 : x6 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5, h6]
  by_cases h7 : x7 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5, h6, h7]
  simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5, h6, h7]
'''
fin='  split <;> (try split) <;> simp_all [fr_none]'
sdefs='Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from'
pat='_ | ⟨b31, _ | ⟨b32, tl⟩⟩'
for i in range(30,-1,-1): pat=f'_ | ⟨b{i}, {pat}⟩'
FR='PRVFresh_R1CandidateWideParserSource_j1'
body=f'''
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PCVH
open AspisR1CandidateParser

abbrev W := field.wide_exact.WideExact

def lm (a b c d : Std.U8) : Std.U32 := core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d])

def dec_cm (x y : Std.U32) : Option field.CM31 :=
  if x >= field.P then none else if y >= field.P then none else some {{ a := x, b := y }}
def dec_qm (c d : Option field.CM31) : Option field.QM31 :=
  match c with | none => none | some c => match d with | none => none | some d => some {{ c0 := c, c1 := d }}
def dec_w (c d : Option field.QM31) : Option W :=
  match c with | none => none | some c => match d with | none => none | some d => some {{ c0 := c, c1 := d }}

theorem fr_none (T : Type) : core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T none = ok none := by
  simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, massert, optionTag, read_discriminant]

theorem cm31_eq ({vs(8)} : Std.U8) (h : [{ls(8)}].length ≤ Usize.max) :
    field.CM31.from_le_bytes ⟨[{ls(8)}], h⟩ = ok (dec_cm {lm(0)} {lm(4)}) := by
  simp [field.CM31.from_le_bytes, field.M31.from_le_bytes, {sdefs}, dec_cm, lm, Array.make]
{fin}

theorem qm31_eq ({vs(16)} : Std.U8) (h : [{ls(16)}].length ≤ Usize.max) :
    field.QM31.from_le_bytes ⟨[{ls(16)}], h⟩ =
      ok (dec_qm (dec_cm {lm(0)} {lm(4)}) (dec_cm {lm(8)} {lm(12)})) := by
  simp [field.QM31.from_le_bytes, {sdefs}, cm31_eq, dec_qm]
  generalize dec_cm {lm(0)} {lm(4)} = c
  generalize dec_cm {lm(8)} {lm(12)} = d
  cases c <;> cases d <;> simp [fr_none]

theorem wide_eq ({vs(32)} : Std.U8) (h : [{ls(32)}].length ≤ Usize.max) :
    field.wide_exact.WideExact.from_le_bytes ⟨[{ls(32)}], h⟩ =
      ok (dec_w (dec_qm (dec_cm {lm(0)} {lm(4)}) (dec_cm {lm(8)} {lm(12)}))
                (dec_qm (dec_cm {lm(16)} {lm(20)}) (dec_cm {lm(24)} {lm(28)}))) := by
  simp [field.wide_exact.WideExact.from_le_bytes, field.wide_exact.WideExact.BYTE_LEN, Slice.len, {sdefs}, qm31_eq, dec_w]
  generalize dec_qm (dec_cm {lm(0)} {lm(4)}) (dec_cm {lm(8)} {lm(12)}) = c
  generalize dec_qm (dec_cm {lm(16)} {lm(20)}) (dec_cm {lm(24)} {lm(28)}) = d
  cases c <;> cases d <;> simp [fr_none]
{chain_text}
theorem main :
    @AspisR1CandidateParser.{FR}.field.wide_exact.WideExact.from_le_bytes =
    @AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes := by
  funext bytes
  obtain ⟨l, hl⟩ := bytes
  by_cases h : l.length = 32
  · rcases l with {pat} <;> first | (exfalso; simp at h; done) | skip
    all_goals
      rw [wide_eq {vs(32)} hl, chain]
      with_unfolding_all rfl
  · unfold AspisR1CandidateParser.{FR}.field.wide_exact.WideExact.from_le_bytes AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
    simp [Slice.len, AspisR1CandidateParser.{FR}.field.wide_exact.WideExact.BYTE_LEN, AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN, h]
end PCVH
#print axioms PCVH.main
'''
open('PRVEq_PCVHs7.lean','w').write(head+body)
P
