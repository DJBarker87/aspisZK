set -e
python3 -B - <<'P'
src=open('inputs/L012_orig.lean').read()
head=src[:src.index('set_option maxHeartbeats 200000 in')]
def vs(n,p='b'): return ' '.join(f'{p}{i}' for i in range(n))
def ls(n,p='b'): return ', '.join(f'{p}{i}' for i in range(n))
def lm(o): return f'(lm b{o} b{o+1} b{o+2} b{o+3})'
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
  simp [field.CM31.from_le_bytes, field.M31.from_le_bytes, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, dec_cm, lm, Array.make, fr_none]
  trace_state
  sorry
end PCVH
'''
open('PRVEq_PCVHs6.lean','w').write(head+body)
P
