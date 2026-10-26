"""Bounded named native transition iterator, shifts, bits and twenty source steps."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
s='''import JFu_TransitionSecond
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionSteps
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal
'''
for i in range(21):s+=f'def r{i:02} : core.ops.range.Range Usize := ⟨{i}#usize,20#usize⟩\n'
for i in range(20):
 s+=f'''theorem next{i:02} : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r{i:02}=
    ok (some {i}#usize,r{i+1:02}) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r{i:02} (by change {i}<20;omega)
  have sameStart : r.start={i+1}#usize := UScalar.eq_of_val_eq (by
    change r.start.val={i+1};change r.start.val={i}+1 at start;omega)
  have same : r=r{i+1:02} := by cases r;simp_all [r{i:02},r{i+1:02}]
  simpa only [same,r{i:02}] using call
#print axioms next{i:02}
'''
for i in range(3,20):
 k=13>>i
 s+=f'''theorem shifted{i:02} : (13#u64 >>> {i}#usize : Result U64)=ok {k}#u64 := by
  have spec : (13#u64 >>> {i}#usize : Result U64) ⦃ out => out.val={k} ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out={k}#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted{i:02}
'''
for i in range(20):
 s+=f'''theorem step{i:02} : validate_transition_loop JFu_PublicSemantic.value r{i:02} 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r{i+1:02} 1#usize := by
'''
 if i==0:s+='  exact JFu_TransitionFirst.step\n'
 elif i==2:s+='  exact JFu_TransitionSecond.step\n'
 elif i==1:s+='''  rw [validate_transition_loop,next01,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_pos (by rfl : 1#usize=1#usize),
    if_pos (by scalar_tac : 1#usize<20#usize),ite_true]
'''
 else:
  k=13>>i;bit=k&1
  s+=f'''  rw [validate_transition_loop,next{i:02},bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬({i}#usize=1#usize)),
    if_neg (by scalar_tac : ¬({i}#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> {i}#usize=ok {k}#u64 := shifted{i:02}
  rw [shifted,bind_tc_ok]
  have bit : lift ({k}#u64 &&& 1#u64)=ok {bit}#u64 := rfl
  rw [bit,bind_tc_ok]
'''
  if bit:s+='  simp only [if_neg (by scalar_tac : ¬(1#u64=0#u64)),bind_tc_ok,Aeneas.Std.uncurry]\n'
  else:s+='  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]\n  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1\n'
  s+='  rfl\n'
 s+=f'#print axioms step{i:02}\n'
s+='''theorem done : validate_transition_loop JFu_PublicSemantic.value r20 1#usize=ok (.Ok ()) := by
  rw [validate_transition_loop]
  rfl
#print axioms done

theorem source : validate_transition_loop JFu_PublicSemantic.value r00 1#usize=ok (.Ok ()) := by
  rw ['''+','.join(f'step{i:02}' for i in range(20))+''',done]
#print axioms source
end AspisR1.JFu_TransitionSteps
end
'''
f=R/'lean/JFu_TransitionSteps.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
print('transition preflight:20 bounded source iterations;17 checked literal shifts;one symbolic aggregation')
