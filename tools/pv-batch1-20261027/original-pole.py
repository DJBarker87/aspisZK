"""Retain the predecessor's flat original-verdict representation in a private cohort.
Not a fresh extraction or a claimed native association by itself.
"""
from pathlib import Path
import subprocess,hashlib,json
E=Path('evidence/pv-batch1-20261027');rev='codex/pv-cb3-20261026';p='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_Op258Ref.lean'
old=subprocess.check_output(['git','show',rev+':'+p],text=True);body=old[old.index('/-- [pv_cb3_kani::reference::equal]'):old.rindex('end R1Z.PV_CB3_Op258Ref')]
header='''-- Flat original-verdict control representation from the predecessor P6 reference.
-- This is not labeled as fresh extraction of the unsupported iterator source.
import PV_B1_258_Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_B1_PoleOriginal
abbrev aspis_core.field.M31 := PV_B1_258.aspis_core.field.M31
abbrev aspis_core.field.CM31 := PV_B1_258.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := PV_B1_258.aspis_core.field.QM31
'''
footer='''#print axioms reference.equal
#print axioms reference.all_slots_clear_loop.body
#print axioms reference.all_slots_clear_loop
#print axioms reference.all_slots_clear
end PV_B1_PoleOriginal
''';s=header+body+footer;(E/'lean/PV_B1_PoleOriginal.lean').write_text(s)
(E/'pole-original-binding.json').write_text(json.dumps(dict(predecessor_revision=subprocess.check_output(['git','rev-parse',rev],text=True).strip(),predecessor_path=p,predecessor_sha256=hashlib.sha256(old.encode()).hexdigest(),representation_sha256=hashlib.sha256(s.encode()).hexdigest(),control_body_verbatim=True,adaptations=['new private module namespace','carrier aliases to the freshly extracted types'],boundary='P6 original-verdict representation; source association is structural and does not itself prove compiler/native adequacy'),indent=2)+'\n')
