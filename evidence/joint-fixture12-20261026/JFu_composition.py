"""Retain the literal native composition suffix after the four successful gathers."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
t=(R/'lean/FIq_Native14.lean').read_text();t=t[t.index('def pool_v1.pair_forest_semantic_terminal.composition_parts\n'):]
a=t.index('      let selectors ←');b=t.index('    | core.ops.control_flow.ControlFlow.Break residual',a)
tail='\n'.join(line[4:] for line in t[a:b].splitlines())+'\n'
tail=tail.replace('selected_claim claims','selected_claim selected').replace('Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter','FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter')
s='''import JFu_CompositionGathers
import JFu_TerminalPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CompositionPrefix
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

def tail (selected : Array field.QM31 84#usize) (a a1 a2 : Array field.QM31 16#usize)
    (mask_only : Array field.QM31 10#usize) :
    Result (core.result.Result (field.QM31 × Array field.QM31 16#usize × Array field.QM31 10#usize ×
      field.QM31 × field.QM31 × field.QM31) PoolV1PairForestSemanticTerminalErrorV1) := do
  let public1 := JFu_PublicSemantic.value
  let o : Option U32 := none
  let point := JFu_TerminalPrefix.alpha
  let lambda := JFu_TerminalPrefix.challenges.lambda
  let chi := JFu_TerminalPrefix.challenges.chi
  let theta := JFu_TerminalPrefix.challenges.theta
'''+tail+'''
theorem source (selected : Array field.QM31 84#usize) : ∃ a b c m,
    composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi JFu_TerminalPrefix.challenges.theta=
      tail selected a b c m := by
  obtain ⟨a,b,c,m,ha,hb,hc,hm⟩ := JFu_CompositionGathers.source selected
  refine ⟨a,b,c,m,?_⟩
  unfold composition_parts
  have noneAmount : JFu_PublicSemantic.value.withdrawal_amount=none := rfl
  rw [noneAmount,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,Bool.false_eq_true,ite_false]
  have updated : {JFu_PublicSemantic.value with withdrawal_amount:=none}=JFu_PublicSemantic.value := rfl
  try rw [updated]
  rw [JFu_Transition.source,bind_tc_ok]
  simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [ha,bind_tc_ok,hb,bind_tc_ok,hc,bind_tc_ok,hm,bind_tc_ok]
  rfl

#print axioms source
end AspisR1.JFu_CompositionPrefix
end
'''
f=R/'lean/JFu_CompositionPrefix.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
