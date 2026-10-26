"""One finite native transition validation step at a time; loop opaque during leaf checks."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
s='''import JFu_PublicSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionSteps
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal
attribute [local irreducible] validate_transition_loop
'''
for i in range(21):s+=f'def r{i:02} : core.ops.range.Range Usize := ⟨{i}#usize,20#usize⟩\n'
for i in range(20):
 s+=f'''theorem step{i:02} : validate_transition_loop JFu_PublicSemantic.value r{i:02} 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r{i+1:02} 1#usize := by
  rw [validate_transition_loop]
  rfl
#print axioms step{i:02}
'''
s+='''theorem done : validate_transition_loop JFu_PublicSemantic.value r20 1#usize=ok (.Ok ()) := by
  rw [validate_transition_loop]
  rfl
#print axioms done
end AspisR1.JFu_TransitionSteps
end
'''
f=R/'lean/JFu_TransitionSteps.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
