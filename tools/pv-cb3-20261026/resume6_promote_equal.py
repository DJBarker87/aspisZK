"""Bind the concretely extracted shipped pole-equality helper to Full carriers."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026'
p=out/'aeneas-source-op258-equal-source-resume6q1/Funs.lean.txt'
s=p.read_text().replace('import PVCB3Op258EqualSource.Types','import R1Z.ProverRwFullExternalFuns')
s=s.replace('namespace PV_CB3_Op258EqualSource','namespace R1Z.PV_CB3_PoleEqualSource').replace('end PV_CB3_Op258EqualSource','end R1Z.PV_CB3_PoleEqualSource')
s=s.replace('namespace R1Z.PV_CB3_PoleEqualSource','namespace R1Z.PV_CB3_PoleEqualSource\nabbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31\nabbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31\nabbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31',1)
t=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_PoleEqualSource.lean'
if '--check' in sys.argv:assert t.read_text()==s
else:t.write_text(s)
(out/'RESUME6_EQUAL_PROMOTION.json').write_text(json.dumps(dict(extraction='aeneas-source-op258-equal-source-resume6q1',original_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),promoted_sha256=hashlib.sha256(s.encode()).hexdigest(),transformations=['namespace/import binding','same M31/CM31/QM31 field carriers bound to existing Full extraction'],arithmetic_changes=0,native_row_credit=False),indent=2)+'\n')
