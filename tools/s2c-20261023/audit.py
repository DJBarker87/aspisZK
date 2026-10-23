#!/usr/bin/env python3
"""Audit local proof claims and receipts without replaying solvers."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2c-20261023'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
base=read(E/'baseline.json')
for path,pin in base['pins'].items():assert sha(R/path)==pin['sha256'],path
receipts=[read(p) for p in sorted(E.glob('*/receipt.json'))]
assert len([r for r in receipts if r['kind']=='lean'])<=100
assert len([r for r in receipts if r['kind']=='kani'])<=60
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 assert r['peak_rss_kib'] and r['source_revision'] and r['source_hashes'] and r['deps_fingerprint']
 assert r['exit_status'] not in [124,137],r['attempt']
accepted=[r for r in receipts if r['exit_status']==0]
lean=[r for r in accepted if r['kind']=='lean']
for p in (D/'lean').glob('S2C_*.lean'):
 text=p.read_text()
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',text,re.M),p
 rr=[r for r in lean if r['source_hashes'].get(p.name)==sha(p)]
 assert len(rr)==1,(p,rr)
 for name in re.findall(r'^theorem (\w+)',text,re.M):
  assert '#print axioms '+name in text,name
  assert any(".{}'".format(name) in l for l in rr[0]['print_axioms']),name
 for l in rr[0]['print_axioms']:
  if 'depends on axioms:' in l:
   axs=l.split('[',1)[1].split(']',1)[0].split(', ')
   assert set(axs)<={'propext','Classical.choice','Quot.sound'},l
for r in accepted:
 if r['kind']=='kani':
  text=(E/r['attempt']/'stdout.log').read_text()
  assert 'VERIFICATION:- SUCCESSFUL' in text,r['attempt']
  assert '[optimized]' in text,r['attempt']
  assert '1 successfully verified harnesses, 0 failures, 1 total' in text,r['attempt']
assert sha(E/'kani-native/src/S2C_trusted.rs')==sha(D/'evidence/s2-trust-20261023/kani-spec/src/lib.rs')
for p,h in read(E/'native-dependencies.json').items():assert sha(R/p)==h,p
inv=read(E/'host-inventory.json');assert inv['all_native_sources_match']
tools=read(D/'evidence/s2-trust-20261023/tool-pins.json')
for key,name in [('lean_binary_sha256','/lean'),('kani_compiler_sha256','/kani-compiler'),('cbmc_sha256','/cbmc')]:
 rows=[r['sha256'] for p,r in inv['files'].items() if p.endswith(name)]
 assert rows==[tools[key]],(key,rows)
# Reuse the actual inherited native GOTO order only at its exact source pin.
orderBase=D/'evidence/s126-current-caller-20261021/sdk-native-step-frames/cleanup-order'
cert=read(orderBase/'certificate.json')
original=D/'evidence/s126-current-caller-20261021/sdk-native-success-bytes-pair/source/src/lib.rs'
assert sha(original)==cert['source_sha256']
assert sha(orderBase/'normal-copy-cleanup-goto.txt')==cert['source_fragment_sha256']
def stage1(text):
 a=text.index('fn stage1(');b=text.index('{',a);depth=0
 for c in range(b,len(text)):
  if text[c]=='{':depth+=1
  elif text[c]=='}':
   depth-=1
   if depth==0:return text[a:c+1]
assert stage1(original.read_text())==stage1((R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text())
assert cert['roles']==['checkpoint','proof_data','statement','public_data','checkpoint_data']
changed=subprocess.check_output(['git','diff','--name-only',base['revision']],cwd=R,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
allowed=[str((D/'lean/S2C_').relative_to(R)),str(E.relative_to(R))+'/',str((D/'design/S2C-20261023.md').relative_to(R)),'tools/s2c-20261023/']
assert all(any(p.startswith(a) for a in allowed) for p in changed),changed
assert not any(p.endswith(('.olean','.elf','.tar','.tar.gz','.out')) for p in changed)
manifest={'schema':'s2c-local-conditional-proof-packet-v1','base_revision':base['revision'],'attempts':[{'attempt':r['attempt'],'kind':r['kind'],'target':r['command'][-1] if r['kind']=='lean' else r['command'][r['command'].index('--harness')+1],'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':int(r['peak_rss_kib']),'swaps':int(r['swaps']),'receipt':r['attempt']+'/receipt.json'} for r in receipts],'accepted_lean':[r['attempt'] for r in lean],'accepted_kani':[r['attempt'] for r in accepted if r['kind']=='kani'],'budget_used':{'lean':sum(r['kind']=='lean' for r in receipts),'kani':sum(r['kind']=='kani' for r in receipts)},'standard_axioms_only':True,'inherited_goto_source_body_equal':True,'inherited_order_roles':cert['roles'],'shipped_files_changed':False,'whole_adapter_certificate_derived':False,'required14_instantiated':False,'target_established':False,'native_instance_obligations':['derive cuts from one accepted execution of adopted adapter','typed SDK Library/heap/metadata interpretation and admission','bind CP source and token/cell geometry to original account records','instantiate per-owner dispatch/capacity/carrier refinements','prove original-to-copy prefix frames and fill concrete accountFrame/writtenMetadata']}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items() if k!='attempts'},indent=2))
