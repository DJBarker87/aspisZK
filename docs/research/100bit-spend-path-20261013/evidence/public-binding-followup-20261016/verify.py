#!/usr/bin/env python3
"""Read/hash-only retained focused results; never compile or extract archives."""
from pathlib import Path,PurePosixPath
import hashlib,json,re,tarfile
H=Path(__file__).resolve().parent;R=H.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
digest=lambda x:sha(json.dumps(x,sort_keys=True).encode())
m=json.loads((H/'manifest.json').read_text());p=H/m['archive']
assert sha(p.read_bytes())==m['archive_sha256'] and p.stat().st_size==m['archive_bytes']
with tarfile.open(p) as t:
 members=t.getmembers();assert len(members)==m['archive_entries']
 assert len({x.name for x in members})==len(members)
 for x in members:
  n=PurePosixPath(x.name);assert not n.is_absolute() and '..' not in n.parts
  assert x.isfile() or x.islnk()
  if x.islnk():assert x.linkname in t.getnames()
 data={x.name:t.extractfile(x).read() for x in members}
entries={line.split('  ',1)[1]:line.split('  ',1)[0] for line in data['SHA256SUMS'].decode().splitlines()}
assert set(entries)==set(data)-{'SHA256SUMS'}
for n,h in entries.items():assert sha(data[n])==h,n
j=lambda n:json.loads(data[n])
snapshot=j('external-inputs.json');keys={};visiting=set()
def key(name):
 if name in keys:return keys[name]
 assert name not in visiting;visiting.add(name);x=snapshot['modules'][name]
 keys[name]=digest({'source':x['source_sha256'],'objects':{s:o['sha256'] for s,o in x['objects'].items()},'imports':{d:key(d) for d in x['imports']},'runtime':snapshot['runtime_files']})
 visiting.remove(name);return keys[name]
finals=m['final_receipts'];expected={'ExtractedPreparationSerializerWhole':('whole-b',2),'ExtractedPublicPreparationBinding':('helper-a',4),'ExtractedFirstCallerReachability':('first-e',3)}
for n,(attempt,count) in expected.items():
 r=j('successful-targets/'+n+'.json');assert r==finals[n]==j('runs/'+attempt+'/'+n+'/receipt.json')
 assert r['exit_status']==0 and r['axioms']['passed'] and len(r['axioms']['reports'])==count
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert not r['dependency_build'] and not r['backend_build']
 assert r['key']['options']==['-j1','-M0'] and r['key']['runtime']==snapshot['runtime_files']
 s=data['sources/'+n+'.lean'];assert s==data['runs/'+attempt+'/'+n+'/source.lean']
 assert s==(R/r['source_manifest_entry']['source']).read_bytes()
 assert sha(s)==r['key']['source_sha256']
 assert not re.search(r'\b(?:sorry|axiom)\b',re.sub(r'/\-.*?\-/','',s.decode(),flags=re.S))
 for suffix,o in r['objects'].items():assert sha(data['objects/'+n+suffix])==o['sha256']
 for dep,item in r['key']['imports'].items():
  if dep in finals:
   prior=finals[dep];assert item=={'receipt_key':digest(prior['key']),'objects':prior['objects']}
  else:assert item=={'closure_key':key(dep),'objects':snapshot['modules'][dep]['objects']}
 log=data['runs/'+attempt+'/'+n+'/lean.log'].decode()
 reports=[{'declaration':name,'axioms':[x.strip() for x in ax.split(',') if x.strip()]} for name,ax in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",log,re.S)]
 reports += [{'declaration':name,'axioms':[]} for name in re.findall(r"'([^']+)' does not depend on any axioms",log)]
 assert reports==r['axioms']['reports']
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
# Pin the newly reused predecessor to its accepted producing archive.
prior=H.parent/'public-preparation-loop-20261016';pm=json.loads((prior/'manifest.json').read_text());pa=prior/pm['archive']
assert sha(pa.read_bytes())==pm['archive_sha256']
with tarfile.open(pa) as t:
 n='ExtractedPreparationSerializerLoop';r=json.load(t.extractfile('successful-targets/'+n+'.json'));x=snapshot['modules'][n]
 assert r['exit_status']==0 and r['axioms']['passed']
 assert sha(t.extractfile('successful-targets/'+n+'.json').read())==x['build_receipt']['sha256']
 assert r['objects']==x['objects'] and r['key']['source_sha256']==x['source_sha256']
# Retain the earlier failed parse without promoting its compiler placeholder axiom.
f=j('runs/frontier-a/ExtractedPreparationSerializerWhole/receipt.json');assert f['exit_status']==1 and not f['axioms']['passed']
assert 'unexpected identifier' in data['runs/frontier-a/ExtractedPreparationSerializerWhole/lean.log'].decode()
# Exact actual first body; opaque/stub boundaries are diagnostic only.
pins=j('first-diagnostic/input/source-pins.json');lib=data['first-diagnostic/input/lib.rs']
for n,h in pins['kit_files'].items():assert sha(data['first-diagnostic/input/'+n])==h
source=(R/pins['source']).read_bytes();a=pins['first'];cut=source[a['start_byte']:a['end_byte_exclusive']]
assert sha(source)==pins['source_file_sha256'] and sha(cut)==a['sha256'] and cut in lib
llbc=j('first-diagnostic/FirstDiagnostic.llbc');assert not llbc['has_errors']
first=[f for f in llbc['translated']['fun_decls'] if f and f['item_meta']['name'][-1].get('Ident',[''])[0]=='first'];assert len(first)==1
assert isinstance(first[0]['body'],dict) and first[0]['item_meta']['opacity']=='Transparent'
assert first[0]['item_meta']['source_text'].encode() in cut
for phase,code in [('charon',0),('aeneas',2)]:
 r=j('first-diagnostic/runs/'+phase+'-a/receipt.json');assert r==m['first_diagnostic_receipts'][phase+'-a']
 assert r['exit_status']==code and r['process_swaps']==r['cgroup_swap_current']==0
 assert r['source_revision']==m['production_source_revision']
 assert r['outputs']['FirstDiagnostic.llbc']==sha(data['first-diagnostic/FirstDiagnostic.llbc'])
log=data['first-diagnostic/runs/aeneas-a/stdout.log'].decode()
assert 'Arrow types are not supported yet' in log and 'SymbolicToPureTypes.ml' in log
assert not any(n.startswith('first-diagnostic/generated/') for n in data)
ext=j('first-diagnostic/runs/aeneas-extended-a/receipt.json')
assert ext==m['first_diagnostic_receipts']['aeneas-extended-a']
assert ext['exit_status']==0 and ext['process_swaps']==ext['cgroup_swap_current']==0
assert ext['outputs']['FirstDiagnostic.llbc']==sha(data['first-diagnostic/FirstDiagnostic.llbc'])
assert ext['tool_pins']['bin/aeneas']=='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
for n,h in ext['outputs'].items():assert sha(data['first-diagnostic/'+n])==h
for n in ext['outputs']:
 if n.startswith('generated-extended/'):
  assert data['first-diagnostic/'+n]==(H/n).read_bytes()
audit=j('extended-tool-audit.json');assert sha(data['extended-tool-audit.json'])==ext['extended_tool_audit_sha256']
assert audit['binary_sha256']==ext['tool_pins']['bin/aeneas'] and len(audit['exact_changed_files'])==38
assert sha(data['tools/aeneas-b59d5188-lean432.patch'])==audit['patch_sha256']=='5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c'
assert data['tools/aeneas-b59d5188-lean432.patch']==(R/'aeneas-verif/lean432/aeneas-b59d5188-lean432.patch').read_bytes()
assert data['tools/patched-aeneas-hashes.sha256']==(R/'aeneas-verif/lean432/patched-aeneas-hashes.sha256').read_bytes()
assert audit['exact_changed_files']=={line.split(None,1)[1]:line.split(None,1)[0] for line in data['tools/patched-aeneas-hashes.sha256'].decode().splitlines()}
assert data['tools/build-patched-aeneas.sh']==(R/'aeneas-verif/v7-tag73-challenge-qm31-source-20260825/toolchain/build-patched-aeneas.sh').read_bytes()
assert sha(data['tools/build-patched-aeneas.sh'])==audit['build_recipe_sha256']
binder=j('first-binder-audit.json');assert binder==json.loads((H/'first-binder-audit.json').read_text())
assert binder['full_first_body_equal_after_boundary_binding'] and len(binder['four_opaque_globals_eliminated'])==4
assert binder['bound_model_sha256']==sha((R/binder['bound_model_source']).read_bytes())
raw=data['first-diagnostic/generated-extended/AspisR1FirstDiagnostic/Funs.lean'].decode();new=(R/binder['bound_model_source']).read_text()
oldfirst=raw[raw.index('def first\n'):raw.rindex('\nend AspisR1FirstDiagnostic')].strip();newfirst=new[new.index('def first {'):new.index('\nprivate theorem bind_success')].strip()
_,body=oldfirst.split(':= do',1);_,nbody=newfirst.split(':= do',1)
for old,replacement in binder['body_replacements']:body=body.replace(old,replacement)
compact=lambda x:re.sub(r'\s+','',x)
assert compact(body).replace('some(mark)','somemark').replace('(error)','error')==compact(nbody)
f=j('runs/first-c/ExtractedFirstCallerReachability/receipt.json');assert f['exit_status']==1 and not f['axioms']['passed']
for tag in ['first-a','first-b']:
 g=j(tag+'.guard.json');assert g['exit_status']==75 and not g['formal_target_started']
assert j('first-d.launcher-failure.json')['formal_target_started']==False
for n in ['stage-host.py','serial-host.py','run-first-diagnostic-host.py','prepare-first-diagnostic.py','audit-extended-host.py','audit-first-binder.py','guard-runner-host.py','run-extended-host.py','bridge-callers.py']:
 assert data['tools/'+n]==(R/'docs/research/100bit-spend-path-20261013/tools/public-binding-followup-kit'/n).read_bytes()
assert data['pack.py']==(H/'pack.py').read_bytes()
print(f'PASS{len(members)} members;9 standard-only reports; helper supplies hs; emitted first prefix supplies hd+fixed supplied public; downstream/custody OPEN')
