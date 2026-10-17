#!/usr/bin/env python3
from pathlib import Path
import json,importlib.util,re,shutil
P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-typedfull-current-20261017');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-finish-a555-proof-20261017');A=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
W.mkdir(exist_ok=True);shutil.copy2(P/'runner.py',W/'runner.py');sp=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r);sha=r.sha
D=json.loads((P/'external-inputs.json').read_text());M=json.loads((P/'sources/SOURCE-MANIFEST.json').read_text());D['roots'].append({'name':'typedfull_current25','source':str(P/'sources'),'objects':str(P/'objects')})
for n in M['topological_order']:
 assert n not in D['modules'],n
 src=P/'sources'/(r.stem(n)+'.lean');rp=P/'successful-targets'/(n+'.json');rc=json.loads(rp.read_text());ob=r.object_pins(P/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['axioms']['passed'] and rc['key']['source_sha256']==sha(src) and rc['objects']==ob
 for dep,di in rc['key']['imports'].items():assert D['modules'][dep]['objects']==di['objects'],(n,dep)
 D['modules'][n]={'root':'typedfull_current25','source':str(src),'source_sha256':sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':sha(rp)}};D['provenance_files'][str(rp)]=sha(rp)
D['roots'].append({'name':'rounds_current_A','source':str(A/'sources'),'objects':str(A/'objects')});aa=[]
for n,run in [('ExtractedSemanticRoundsModel','model-d'),('ExtractedSemanticRoundsReachability','reach-d')]:
 rp=A/'runs'/run/'receipt.json';ip=A/'runs'/run/'input-manifest.json';lp=A/'runs'/run/'lean.log';rc=json.loads(rp.read_text());im=json.loads(ip.read_text());src=A/'sources'/(n+'.lean');ob=r.object_pins(A/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['input_manifest_sha256']==sha(ip) and rc['source_sha256']==sha(src)==im['sources'][n+'.lean'] and rc['olean_sha256']==ob['.olean']['sha256'];assert r.audits(src,lp.read_text())['passed']
 for dep in r.imports(src,True):
  v=D['modules'][dep]
  if dep=='ExtractedSemanticRoundsModel':assert v['source_sha256']==im['sources'][dep+'.lean']
  elif dep in im['current_canonical_and_begin_pins']:
   q=im['current_canonical_and_begin_pins'][dep];assert q['source_sha256']==v['source_sha256'] and q['object_sha256']==v['objects']['.olean']['sha256']
  elif dep in im['backend_object_pins']:
   q=im['backend_object_pins'][dep];assert q['source_sha256']==v['source_sha256'] and q['object_sha256']==v['objects']['.olean']['sha256']
 for dep,q in im['current_canonical_and_begin_pins'].items():assert q['source_sha256']==D['modules'][dep]['source_sha256'] and q['object_sha256']==D['modules'][dep]['objects']['.olean']['sha256']
 for dep,q in im['backend_object_pins'].items():
  if dep not in D['modules']:continue # Unimported backend compiler/meta modules are outside the model closure.
  assert q['source_sha256']==D['modules'][dep]['source_sha256'] and q['object_sha256']==D['modules'][dep]['objects']['.olean']['sha256']
 D['modules'][n]={'root':'rounds_current_A','source':str(src),'source_sha256':sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':sha(rp)}}
 for f in [rp,ip,lp]:D['provenance_files'][str(f)]=sha(f)
 aa.append({'module':n,'receipt_sha256':sha(rp),'input_manifest_sha256':sha(ip),'all_backend_and_current_base_source_and_object_pins_equal':True})
r.dump(W/'rounds-cache-audit.json',aa);D['provenance_files'][str(W/'rounds-cache-audit.json')]=sha(W/'rounds-cache-audit.json')
mods={}
for n in ['ExtractedVerifyFinishModel','ExtractedVerifyFinishReachability']:
 src=W/'sources'/(n+'.lean');mods[n]={'stage_as':n+'.lean','source_sha256':sha(src),'imports':r.imports(src),'source_revision':'a555c852664c80000942f0c911e16719a5493625','source':n+'.lean','role':'Complete actual finish with fixed actual RoundModel and explicit arithmetic boundaries','axiom_requests':len(re.findall(r'^#print axioms ',src.read_text(),re.M))}
r.dump(W/'external-inputs.json',D);r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':list(mods),'groups':{}});print('STAGED2; typedFull25 and A2 producing import identity verified; no Lean launched')
