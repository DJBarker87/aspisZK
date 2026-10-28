"""Emit the fixed-index copy residual proof and compose the actual copy stage."""
from pathlib import Path
import sys,json
ns={};s=Path('tools/pv-b3p6-20261028/success227_resume6.py').read_text();exec(s.split("emit('PV_B3P_HostSuccess227'",1)[0],ns)
# The generator runs in a tiny task-local temporary output directory; --check
# never mutates the tracked proof source.
import tempfile,shutil
p=Path('evidence/pv-b3p6-20261028/lean/PV_B3P_CopySuccess227.lean')
with tempfile.TemporaryDirectory(dir='tools/pv-b3p6-20261028',prefix='.copygen-') as tmp:
 ns['L']=Path(tmp)
 shutil.copy2('evidence/pv-b3p6-20261028/lean/PV_B3P_E227_16.lean',ns['L']/'PV_B3P_E227_16.lean')
 saved_args=sys.argv[:];sys.argv=[a for a in sys.argv if a!='--check']
 try:ns['emit']('PV_B3P_CopySuccess227','PV_B3P_E227_16',['reference_copy_terminal.copy_residual'],['PV_B3P_CopyLoopSuccess227'])
 finally:sys.argv=saved_args
 data=(ns['L']/'PV_B3P_CopySuccess227.lean').read_text()
data=data.replace('end PV_B3P_Success227','''/-- Successful execution of the entire actual owned copy evaluator, for
arbitrary field payloads and both public variants. This is not full op227. -/
theorem copy_success (openings : Array aspis_core.field.QM31 16#usize)
    (h1_z : aspis_core.field.QM31) (selectors : reference_copy_terminal.Selectors)
    (lambda chi : aspis_core.field.QM31) (append_index : U64)
    (variant : reference_copy_terminal.PoolV1PairForestCompiledVariantV1) :
    Success (reference_copy_terminal.evaluate_with_selectors openings h1_z selectors lambda chi append_index variant) := by
  unfold reference_copy_terminal.evaluate_with_selectors
  apply bind
  · exact patterns_total openings lambda
  intro patterns
  apply bind
  · exact copy_loop_total selectors append_index variant patterns _ _ _ _ 0#usize
      (by change 0≤136; omega)
  rintro ⟨pv,pw,cv,cw⟩
  apply bind
  · exact active_total selectors
  intro active
  apply bind
  · exact total_reference_copy_terminal_copy_residual _ h1_z chi
  intro residual
  apply bind
  · exact qmul active residual
  intro weighted
  exact ok _

#print axioms copy_success
end PV_B3P_Success227''')
if '--check'in sys.argv:
 assert p.read_text()==data,p
else:
 p.write_text(data);Path('evidence/pv-b3p6-20261028/resume7/copy-generator.json').write_text(json.dumps(ns['records'],indent=2)+'\n')
