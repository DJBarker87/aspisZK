#!/usr/bin/env python3
"""Exact published caller-cut types for the S6 consumer; no producer rewrite."""
from pathlib import Path
import subprocess,hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';P=B/'evidence/s126-current-caller-20261021/s6-sdk-source-cuts-20261024';P.mkdir(exist_ok=True)
rev='97caa13d92';rows=[];pieces=[]
def take(n,start,end,header,footer):
 path=str((B/'lean'/(n+'.lean')).relative_to(R));src=subprocess.check_output(['git','show',rev+':'+path]).decode();a=src.index(start);b=src.index(end,a);body=src[a:b];pieces.append(header+body+footer);rows.append(dict(module=n,path=path,revision=rev,source_sha256=hashlib.sha256(src.encode()).hexdigest(),start=start,end=end,header=header,footer=footer,body_sha256=hashlib.sha256(body.encode()).hexdigest()))
take('AdapterRwLeadInputs','abbrev Public :=','/-- OPEN','namespace AspisR1.AdapterRw.LeadInputs\n','end AspisR1.AdapterRw.LeadInputs\n')
take('S2W_NativeConsolidation','structure FirstCut where','/-- No source-cut hypotheses','namespace AspisR1.S2W_NativeConsolidation\nopen S2W_ExtractionBoundary MultiproofConeCanonical\n','end AspisR1.S2W_NativeConsolidation\n')
text='import S6SdkDependencyFactorV1\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result\n'+ '\n'.join(pieces)
p=S/'S6SdkSourceCutTypesV1.lean';m=dict(schema='focused-extractor-proof-packet-v1',selections=rows,source=str(p.relative_to(R)),source_sha256=hashlib.sha256(text.encode()).hexdigest())
if '--check' in sys.argv:assert p.read_text()==text and json.loads((P/'declarations.json').read_text())==m
else:p.write_text(text);(P/'declarations.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps(dict(status='PASS',selections=len(rows),bytes=len(text.encode()))))
