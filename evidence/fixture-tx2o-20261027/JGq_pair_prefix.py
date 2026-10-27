from pathlib import Path
import re,textwrap,sys
R=Path(__file__).resolve().parents[2];s=(R/'lean/FIo_NativeFuns.lean').read_text();s=s[s.index('def _root_.FIo_Native.weights.Weights.pair\n'):]
s=s[s.index('      let (r1, _, parts1) ←'):s.index('    | core.result.Result.Err _ =>')]
s=textwrap.dedent(s).replace('aspis_core.','FIo_Native.aspis_core.').replace('transport.','FIo_Native.transport.').replace('verifier.','FIo_Native.verifier.')
for a,b in [('self','w'),('shared_two_point','true'),('folds','2#usize'),('n','64#usize'),('ap0','JGq_Powers0.a4'),('ap1','JGq_Powers1.a4'),('v','scratch'),('parts','initial')]:s=re.sub(r'\b'+a+r'\b',b,s)
s='\n'.join('  '+line for line in s.splitlines())
t='''import JGq_PairShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PairPrefix
open Aeneas Aeneas.Std Result ControlFlow
open JGq_PairShape
abbrev E := FIo_Install.NE
def initial : Array E 7#usize := Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO

/-- Exact computation after the proved shape, power, allocation and shared
branch-selection prefix. Every remaining source call and error stays explicit. -/
def remaining : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
'''+s+'''

/-- No successful Pair call or final gate is a premise. -/
theorem native : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))
    w alpha f kappa=remaining := by
  unfold FIo_Native.weights.Weights.pair
  rw [length,divided,bind_tc_ok,folds,expected,bind_tc_ok]
  have different : (64#usize != 64#usize)=false := by decide
  simp only [different,Bool.false_eq_true,ite_false,ite_true]
  rw [read0,bind_tc_ok,JGq_Powers0.source,bind_tc_ok,read1,bind_tc_ok,JGq_Powers1.source,bind_tc_ok,
    filled,bind_tc_ok]
  rw [JGo_TX2_PairGuard.source,bind_tc_ok]
  rfl
#print axioms native

def adapted : Result (core.result.Result AspisR1Stage2.Stage2Finish.E AspisR1Stage2.verifier.Error) := do
  let r ← remaining
  match r with
  | .Ok out=>ok (.Ok (FIo_Install.fromE out))
  | .Err e=>ok (.Err (FIo_Install.error e))

theorem source : FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
    (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=adapted := by
  unfold FIo_Install.pair adapted
  rw [native]
#print axioms source
end AspisR1.JGq_PairPrefix
end
'''
p=R/'lean/JGq_PairPrefix.lean'
if '--check' in sys.argv:assert p.read_text()==t
else:p.write_text(t)
print('actual Pair prefix generated; all remaining source carriers retained')
