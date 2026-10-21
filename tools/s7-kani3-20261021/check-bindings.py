#!/usr/bin/env python3
"""Check additive ports against pinned emitted declarations, modulo carrier names."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s7-kani3-20261021'
generated=B/'evidence/s7-kani-20261021/extraction/generated/S7OwnedP6/Funs.lean'
s=generated.read_text();results=[]
for name,module in [('inverse_owned','S7Kani3InverseLoop'),('groups_owned','S7Kani3GroupsLoop')]:
 original=s[s.index('def '+name+'\n'):];original=original[:original.index('partial_fixpoint')+len('partial_fixpoint')]
 port=(B/'lean'/(module+'.lean')).read_text();port=port[port.index('def '+name+'\n'):];port=port[:port.index('partial_fixpoint')+len('partial_fixpoint')]
 normalized=original.replace('aspis_core.field.M31.mul','AspisR1Qm31ArithmeticProbe.field.M31.mul').replace('aspis_core.field.M31','U32')
 assert re.sub(r'\s+','',normalized)==re.sub(r'\s+','',port),module
 results.append(dict(module=module,declaration=name,generated_sha256=hashlib.sha256(original.encode()).hexdigest(),port_sha256=hashlib.sha256(port.encode()).hexdigest(),substitutions={'aspis_core.field.M31':'U32','aspis_core.field.M31.mul':'AspisR1Qm31ArithmeticProbe.field.M31.mul'},matches=True))
(E/'loop-bindings.json').write_text(json.dumps(dict(generated_file=str(generated.relative_to(R)),generated_sha256=hashlib.sha256(generated.read_bytes()).hexdigest(),declarations=results),indent=2)+'\n')
print('Two exact emitted recurrence bindings pass')
