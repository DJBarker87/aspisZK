#!/usr/bin/env python3
"""Factor complete self-contained emitted definitions; never import templates."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s126-current-caller-20261021/s1-claims-nuc-extract-run10/generated/AspisS1ClaimsUnrolledSource/Funs.lean';raw=p.read_text();matches=list(re.finditer(r'(?m)^def\s+([A-Za-z0-9_.]+)',raw))
parts=[];pins=[]
for k,m in enumerate(matches):
 name=m[1]
 if name in ['aspis_core.r0.heap.filled','candidate_claims.claims']:continue
 start=raw.rfind('/--',0,m.start());end=raw.rfind('/--',0,matches[k+1].start())if k+1<len(matches)else raw.index('\nend AspisS1ClaimsUnrolledSource',m.end())
 chunk=raw[start:end];assert chunk.count('\ndef ')+chunk.count('\ndef\n')==1,name
 parts.append(chunk);pins.append(dict(name=name,sha256=hashlib.sha256(chunk.encode()).hexdigest()))
s='import S1ClaimsUnrolledTypesV1\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnoncomputable section\nnamespace AspisS1ClaimsUnrolledSource\n\n'+''.join(parts)+'\nend AspisS1ClaimsUnrolledSource\n'
for name in ['core.result.Result.map_err','aspis_core.field.QM31.Insts.CoreCloneClone.clone','aspis_core.field.QM31.ZERO','r1_wire.Prefix.record','r1_wire.Prefix.validated_record']:s+='\n#print axioms AspisS1ClaimsUnrolledSource.'+name+'\n'
out=B/'lean-candidates/s126-caller-boundary-20261021/S1ClaimsUnrolledHelpersV1.lean';assert not out.exists();out.write_text(s)
(Path(__file__).parent/'helpers-binding.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),maintained_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),complete_declarations=pins,resource_option_overrides=False,external_templates_imported=False),indent=2)+'\n')
