#!/usr/bin/env python3
"""Prepare maintained types without importing generated axiom templates/options."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
raw=B/'evidence/s126-current-caller-20261021/s1-claims-nuc-extract-run10/generated/AspisS1ClaimsUnrolledSource/Types.lean'
s=raw.read_text();assert 'core.mem.alignment.Alignment' not in s
s=s.replace('import AspisS1ClaimsUnrolledSource.TypesExternal\n','')
s=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) [0-9]+\n','',s,flags=re.M)
changes=[]
for ns in ['aspis_core.r0','r1_wire']:
 start=s.index('@[discriminant isize',s.index('/-- [aspis_core::r0::Error]'if ns=='aspis_core.r0'else'/-- [aspis_r1_cost_probe::r1_wire::Error]'))
 end=s.index('\n/--',start)
 start=s.rfind('/--',0,start)
 old=s[start:end];new='namespace '+ns+'\n'+old.replace(ns+'.Error','Error')+'\nend '+ns+'\n'
 s=s[:start]+new+s[end:];changes.append(dict(namespace=ns,qualification='same full type/constructor names; derived instance namespace explicitly repinned to avoid duplicate instDiscriminantErrorIsize'))
s+='\n#print axioms AspisS1ClaimsUnrolledSource.alloc.collections.TryReserveErrorKind\n#print axioms AspisS1ClaimsUnrolledSource.aspis_core.field.QM31\n#print axioms AspisS1ClaimsUnrolledSource.r1_wire.Prefix\n#print axioms AspisS1ClaimsUnrolledSource.r1_wire.ValidatedRecord\n#print core.alloc.layout.Layout\n'
out=B/'lean-candidates/s126-caller-boundary-20261021/S1ClaimsUnrolledTypesV1.lean';out.write_text(s)
(Path(__file__).parent/'types-binding.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),maintained_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),changes=changes,resource_options_removed=True,unused_external_import_removed='alignment is not referenced by this generated types module; no dummy or opaque type installed',raw_templates_imported=False),indent=2)+'\n')
