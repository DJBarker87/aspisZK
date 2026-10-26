"""Joint partial fixture: reuse the checked predecessor; retain the native unresolved tails explicitly."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
s=(R/'lean/JFu_FinishInputs.lean').read_text();a=s.index(' := by',s.index('theorem inhabited'));s=s[:a]
s='import JFu_FinishInputs\nimport JFu_CompositionPrefix\n'+s
s=s.replace('namespace AspisR1.JFu_FinishInputs','namespace AspisR1.JFu_PartialFixture')
s=s.replace('(mask : aspis_core.field.QM31),','''(mask : aspis_core.field.QM31)
      (selected : Array FIq_Native.field.QM31 84#usize)
      (a b c : Array FIq_Native.field.QM31 16#usize) (m : Array FIq_Native.field.QM31 10#usize),
    (''')
s+=''' ) ∧
    FIq_Native.array_from_fn_copy 84#usize FIq_Native.field.QM31.Insts.CoreMarkerCopy
      FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      FIq_Native.field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.validate_transition JFu_PublicSemantic.value=ok (.Ok ()) ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (FIq_Carriers.toPublic JFs_PublicSerialization.value) JFu_TerminalCallback.claims
      JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges=JFu_TerminalPrefix.tail selected ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts JFu_PublicSemantic.value selected
      JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta=JFu_CompositionPrefix.tail selected a b c m := by
  obtain ⟨expanded,y1,pre,view,claims,cs,mask,old⟩ := JFu_FinishInputs.inhabited D B hash
  obtain ⟨selected,gather,validated,native⟩ := JFu_TerminalPrefix.source
  obtain ⟨a,b,c,m,composition⟩ := JFu_CompositionPrefix.source selected
  exact ⟨expanded,y1,pre,view,claims,cs,mask,selected,a,b,c,m,old,gather,validated,native,composition⟩

#print axioms inhabited
end AspisR1.JFu_PartialFixture
'''
f=R/'lean/JFu_PartialFixture.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
