"""Promote only the closed owned selector from the tensor extraction."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026'
p=out/'aeneas-source-op253-tensor-ref-resume6host007/Funs.lean.txt';s=p.read_text()
start=s.index('/-- [pv_cb3_source::resume6_tensor_reference::pick4]')
end=s.index('/-- [pv_cb3_source::resume6_tensor_reference::plane]')
body=s[start:end]
assert 'QM31.mul' not in body and 'QM31.ONE' not in body
header='''import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result ControlFlow Error
namespace R1Z.PV_CB3_WeightsPickSource
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
'''
result=header+body+'end R1Z.PV_CB3_WeightsPickSource\n'
t=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_WeightsPickSource.lean'
if '--check' in sys.argv:assert t.read_text()==result
else:t.write_text(result)
(out/'RESUME6_PICK_PROMOTION.json').write_text(json.dumps(dict(extraction='aeneas-source-op253-tensor-ref-resume6host007',original_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),promoted_sha256=hashlib.sha256(result.encode()).hexdigest(),transformations=['select exactly the emitted pick4 definition','namespace/import and matching QM31 carrier binding'],arithmetic_changes=0,callee_boundaries=[],whole_tensor_closed=False,native_row_credit=False),indent=2)+'\n')
