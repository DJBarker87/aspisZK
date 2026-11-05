from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent
path='evidence/finish-install2-20261026/FIo_014/sources/FIo_NativeFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+path],text=True)
a=s.index('def _root_.FIo_Native.weights.factored_s2_libra_weights_loop.body')
b=s.index('/-- [aspis_r1_cost_probe::weights::factored_s2_libra_weights]: loop 0:',a)
body=s[a:b];tail=body[body.index('    let low ←'):]
# The two producer arrays are exactly the tuple retained by NHI_.
tail=tail.replace('(Array.make 4#usize [ aspis_core.field.QM31.ONE, q1, q2, q3 ])','low_powers')
tail=tail.replace('(Array.make 4#usize [ aspis_core.field.QM31.ONE, q41, q8, q12 ])','high_powers')
tail=tail.replace('q41','q4')
header='''import NHI_FactoredProducers
import NHI_RangeProgress
set_option autoImplicit false
noncomputable section
namespace NHM_FactoredPrefix
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues FIo_Native
abbrev Iter := NHI_RangeProgress.Range
abbrev Cells := Array NE 4#usize
abbrev State := Iter × Cells

/-- Source suffix after the retained eight-call producer packet. -/
def tail (ap0 ap1 : Array NE 4#usize) (side : Usize) (iter1 : Iter) (weights : Cells)
 (low_powers high_powers : Array NQ 4#usize) (q4 q16 : NQ) : Result (ControlFlow State Cells) := do
'''
header+='\n'.join(line[4:] if line.startswith('    ')else line for line in tail.rstrip().splitlines())+'\n\n'
header+='''def body (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize) (s : State) :
 Result (ControlFlow State Cells) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some side=>do
  let q ← Array.index_usize extra side
  let (low,high,q4,q16) ← NHI_FactoredProducers.run q
  tail ap0 ap1 side next s.2 low high q4 q16

theorem pick_two (q0 q1 q2 q3 : NQ) :
 Array.index_usize (Array.make 4#usize [q0,q1,q2,q3]) 2#usize=ok q2 := by rfl

/-- Complete source-order association, retaining the unused q^4 call and every
possible producer error. No successful-child or desired-output premise. -/
theorem source (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize) (s : State) :
 FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra s.1 s.2=
 body ap0 ap1 extra s := by
 unfold FIo_Native.weights.factored_s2_libra_weights_loop.body body tail NHI_FactoredProducers.run
 simp only [NHI_FactoredProducers.one,bind_assoc_eq,bind_tc_ok,pick_two]
 rfl

#print axioms pick_two
#print axioms source
end NHM_FactoredPrefix
end
'''
(E/'NHM_FactoredPrefix.lean').write_text(header)
(E/'NHM_FACTORED_PREFIX_INPUT.json').write_text(json.dumps(dict(path=path,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sha256=hashlib.sha256(s.encode()).hexdigest(),purpose='source suffix copied and proved against selected emitted body; only producer-array names and q41 name substituted; no field definitions unfolded'),indent=2)+'\n')
