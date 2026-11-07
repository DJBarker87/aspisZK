"""Prepare hash-linked standalone archive inputs and explicit configurations."""
import ast,json,subprocess,hashlib,lzma,collections,re
from pathlib import Path
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/codex-cx-emission-repro2-20261110'
sha=lambda b:hashlib.sha256(b).hexdigest()
def blob(p):return subprocess.check_output(['git','show','HEAD:'+p])
def write(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
def recover(r):
 s=r['source'];h=r['reference_sha256']
 if s['paths']:
  p=min(s['paths'],key=lambda p:('/sources/' not in p,len(p)));b=blob(p);basis=dict(path=p,git_blob=s['git_blob'])
 else:
  x=s['embedded'][0];p=x['container_paths'][0];b=blob(p);d=json.loads(lzma.decompress(b) if p.endswith('.xz') else b)
  b=next(f['contents'].encode() for f in d['translated']['files'] if f and isinstance(f.get('contents'),str) and sha(f['contents'].encode())==h)
  basis=dict(embedded=x,git_blob=s['git_blob'])
 assert sha(b)==h
 return b,basis
plan=json.load(open(E/'NML_INPUT_MAP.json'));runs=[];seen={};unready=[]
for g in plan['groups']:
 for r in g['mappings']:
  cc=r['charon_command'];ac=r['aeneas_command'];oldmanifest=cc[cc.index('--manifest-path')+1]
  # Recover the exact original manifest literal from the producing job's extraction source.
  script=None;manifest=None
  for receipt in r['receipt_paths']:
   packet='/'.join(receipt.split('/')[:2]);prefix=Path(receipt).name.split('_')[0]
   if '/stdout.log' in receipt:
    script_paths=[receipt.rsplit('/',1)[0]+'/sources/'+prefix+'_extract.py',packet+'/'+prefix+'_extract.py']
    prefix=receipt.split('/')[-2].split('_')[0];script_paths=[receipt.rsplit('/',1)[0]+'/sources/'+prefix+'_extract.py',packet+'/'+prefix+'_extract.py']
   else:
    attempt=Path(receipt).name.split('-')[0];script_paths=[packet+'/'+attempt+'/sources/'+prefix+'_extract.py',packet+'/'+prefix+'_extract.py']
   for sp in script_paths:
    try:raw=blob(sp);tree=ast.parse(raw)
    except (subprocess.CalledProcessError,SyntaxError):continue
    candidates=[]
    for n in ast.walk(tree):
     if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='write_text' and n.args and isinstance(n.args[0],ast.Constant) and isinstance(n.args[0].value,str) and '[package]' in n.args[0].value:candidates.append(n.args[0].value)
    if len(candidates)==1:manifest=candidates[0].encode();script=dict(path=sp,git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+sp],text=True).strip(),sha256=sha(raw));break
   if manifest:break
  if not manifest:
   unready.append(dict(group=g['group'],receipt=r['receipt_paths'],reason='Exact standalone Cargo.toml not recovered from producing script'));continue
  if '[dependencies]' in manifest.decode():
   unready.append(dict(group=g['group'],receipt=r['receipt_paths'],reason='Reference dependency closure needs separate recovery'));continue
  b,basis=recover(r)
  key=json.dumps([r['reference_sha256'],cc[1:cc.index('--dest-file')],cc[cc.index('--manifest-path')+2:],ac[1:ac.index('-dest')]])
  if key in seen:
   q=seen[key]
   q['groups']=sorted(set(q['groups']+[g['group']]));q['members']=sorted(set(q['members']+g['members']));continue
  q=dict(groups=[g['group']],members=g['members'][:],bytes=g['bytes'],configuration=r,reference_basis=basis,manifest_basis=script,reference_sha256=sha(b),manifest_sha256=sha(manifest),original_manifest=oldmanifest,charon_command=cc.copy(),aeneas_command=ac.copy())
  q['_source']=b;q['_manifest']=manifest;seen[key]=q;runs.append(q)
# One per group before variant configurations; smallest groups first.
counts=collections.Counter()
for q in runs:q['variant_rank']=min(counts[g] for g in q['groups']);counts.update(q['groups'])
runs.sort(key=lambda q:(q['variant_rank'],q['bytes']))
for i,q in enumerate(runs,1):
 a='NML_E%03d'%i;q['run']=a;ref='NML_inputs/'+a;out=H+'/'+a+'_emitted'
 for n,raw in [('src/lib.rs',q.pop('_source')),('Cargo.toml',q.pop('_manifest'))]:
  p=E/ref/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
 q['reference_directory']=ref;q['charon_command'][q['charon_command'].index('--manifest-path')+1]=H+'/'+ref+'/Cargo.toml';q['charon_command'][q['charon_command'].index('--dest-file')+1]=out+'/repro.llbc'
 q['aeneas_command'][q['aeneas_command'].index('-dest')+1]=out+'/raw';q['aeneas_command'][-1]=out+'/repro.llbc'
 q['opacity']=[dict(path=q['charon_command'][j+1],why='Exact producing-job archived opacity') for j,x in enumerate(q['charon_command'][:-1]) if x=='--opaque']
 q['relocation']='Only input/output paths relocated; original standalone manifest and source bytes retained, original flags preserved. Frozen release graph validated separately by unchanged NHR_stage.extract.'
 write(E/(a+'_spec.json'),q)
 inputs=['NML_extract.py','NML_NHR_stage.py','NML_STAGER_PIN.json','NML_STAGING_MANIFEST.json','NML_FROZEN_PAYLOAD.json.sha256',a+'_spec.json',ref+'/src/lib.rs',ref+'/Cargo.toml']
 cfg=dict(attempt=a,kind='extract',module=','.join(q['groups']),sources=inputs,upload=inputs+['NML_FROZEN_PAYLOAD.json.xz'],command=['python3','NML_extract.py',a],collect=[a+'_emitted','NML_TOOL_ATTEMPTS.jsonl'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'},deps_fingerprint={},expected_time='Optimized pinned Charon on tiny archived standalone reference, then sequential Aeneas; frozen graph preflight reused source staging')
 write(E/(a+'.json'),cfg)
write(E/'NML_PLAN.json',dict(budget=dict(Charon=40,Aeneas=40,Lean=20,Kani=0),runs=runs,unready=unready,ordering='Smallest aggregate committed size; one per recovered group before distinct archived variants; never rerun same command/input'))
print(json.dumps(dict(runs=len(runs),unready=len(unready),groups=len({g for q in runs for g in q['groups']}))))
