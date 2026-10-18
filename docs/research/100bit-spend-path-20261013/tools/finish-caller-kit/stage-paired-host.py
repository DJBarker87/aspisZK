#!/usr/bin/env python3
from pathlib import Path
import json,importlib.util,re,shutil
P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-finish-a555-proof-20261017');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-paired-current-20261017');A=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
W.mkdir(exist_ok=True);shutil.copy2(P/'runner.py',W/'runner.py');sp=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r);sha=r.sha
D=json.loads((P/'external-inputs.json').read_text());M=json.loads((P/'sources/SOURCE-MANIFEST.json').read_text());D['roots'].append({'name':'finish_actual25','source':str(P/'sources'),'objects':str(P/'objects')})
for n in M['topological_order']:
 assert n not in D['modules'],n
 src=P/'sources'/(r.stem(n)+'.lean');rp=P/'successful-targets'/(n+'.json');rc=json.loads(rp.read_text());ob=r.object_pins(P/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['axioms']['passed'] and rc['key']['source_sha256']==sha(src) and rc['objects']==ob
 for dep,di in rc['key']['imports'].items():assert D['modules'][dep]['objects']==di['objects'],(n,dep)
 D['modules'][n]={'root':'finish_actual25','source':str(src),'source_sha256':sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':sha(rp)}};D['provenance_files'][str(rp)]=sha(rp)
mods={}
for n in ['ExtractedFirstPairedReachability']:
 src=W/'sources'/(n+'.lean');mods[n]={'stage_as':n+'.lean','source_sha256':sha(src),'imports':r.imports(src),'source_revision':'a555c852664c80000942f0c911e16719a5493625','source':n+'.lean','role':'Complete actual finish with fixed actual RoundModel and explicit arithmetic boundaries','axiom_requests':len(re.findall(r'^#print axioms ',src.read_text(),re.M))}
r.dump(W/'external-inputs.json',D);r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':list(mods),'groups':{}});print('STAGED1 actual first paired caller; predecessor3 current source/object/import keys verified')
