#!/usr/bin/env python3
"""Read/hash-only actual primitive + fresh conditional-core packet verifier."""
from pathlib import Path
import hashlib,json,re,tarfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=BASE/'evidence/c2-host-embedding-20261017'
sha=lambda b:hashlib.sha256(b).hexdigest()
def reports(log):
 return [(m[0],set(x.strip() for x in m[1].split(',') if x.strip())) for m in
  re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)]
def main():
 archive=E/'embedding-checkpoint.tar.gz';assert sha(archive.read_bytes())=='ca8095e32c8a8e4f82f2378b8ad6d04d5d1d6cdbd92ed8f5b36b23f173ad41b3'
 members=json.loads((E/'embedding-members.json').read_text())
 with tarfile.open(archive) as tf:files={m.name:tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
 assert set(files)==set(members)
 for n,b in files.items():assert sha(b)==members[n]['sha256'] and len(b)==members[n]['bytes'],n
 for prefix in ['extraction/runs/charon-a','extraction/runs/aeneas-a']:
  r=json.loads(files[prefix+'/receipt.json']);assert r['exit_status']==0 and r['process_swaps']==0
 assert json.loads(files['extraction/C2OwnedHost.llbc'])['has_errors']==False
 pins=json.loads(files['extraction/input/source-pins.json'])
 for n,h in pins['kit_files'].items():assert sha(files['extraction/input/'+n])==h
 assert (E/'translation.json').read_bytes()==files['extraction/generated/translation.json']
 for n in ['Types.lean','Funs.lean']:
  b=files['extraction/generated/AspisC2HostEmbedding/'+n]
  assert b==files['lean/sources/AspisC2HostEmbedding/'+n]
  assert b==(BASE/'lean/c2-host-embedding-20261017/AspisC2HostEmbedding'/n).read_bytes()
  assert b'axiom ' not in b
 allowed={'propext','Classical.choice','Quot.sound'}
 successful={'primitive-types-b':'AspisC2HostEmbedding.Types','primitive-funs-a':'AspisC2HostEmbedding.Funs','primitive-proof-b':'C2HostEmbedding','primitive-core-b':'C2HostEmbeddingConstruction'}
 all_reports=[]
 for attempt,module in successful.items():
  prefix='lean/runs/'+attempt;r=json.loads(files[prefix+'/receipt.json'])
  assert r['target']==module and r['exit_status']==0 and r['source_revision']=='6aafe82a8'
  assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
  assert r['external_lean_prelaunch']==[] and r['external_lean_overlap']==[]
  assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
  assert r['reservation']['total_memory_max_bytes']<r['reservation']['safe_limit_bytes']
  assert sha(files['lean/input-manifest.json'])==r['input_manifest_sha256']
  assert sha(files['lean/primitive-environment.json'])==r['environment_sha256']
  assert sha(files[prefix+'/runner.py'])==r['runner_sha256']
  source=files[prefix+'/source.lean'];assert sha(source)==r['source_sha256']
  assert source==files['lean/sources/'+module.replace('.','/')+'.lean']
  assert sha(files['lean/objects/'+module.replace('.','/')+'.olean'])==r['olean_sha256']
  if module.startswith('C2'):
   assert source==(BASE/'lean'/str(module+'.lean')).read_bytes()
  log=files[prefix+'/lean.log'].decode();assert 'sorryAx' not in log and 'error:' not in log
  rs=reports(log);assert all(xs<=allowed for _,xs in rs)
  if module=='C2HostEmbedding':assert len(rs)==20
  if module=='C2HostEmbeddingConstruction':assert len(rs)==8 and sum(xs=={'propext'} for _,xs in rs)==6
  all_reports+=rs
 for attempt in ['primitive-types-a','primitive-proof-a','primitive-core-a']:
  assert json.loads(files['lean/runs/'+attempt+'/receipt.json'])['exit_status']==1
 # This is a namespace-only reuse of the old generic core, checked again here.
 old=(BASE/'lean/C2OwnedHostConstruction.lean').read_text();new=(BASE/'lean/C2HostEmbeddingConstruction.lean').read_text()
 core=old[old.index('abbrev Rows'):old.index('open ExactLeafFieldCodec')].strip()
 assert new[new.index('abbrev Rows'):new.index('#print axioms run_of_steps')].strip()==core
 assert [line for line in new.splitlines() if line.startswith('import ')]==['import C2HostEmbedding']
 a=json.loads(files['lean/primitive-dependency-audit.json']);snapshot=json.loads(files['lean/current-external-inputs.json'])
 assert sha(files['lean/current-external-inputs.json'])==a['external_snapshot_sha256']
 assert sha(files['lean/primitive-environment.json'])==a['environment_sha256']
 assert a['module_count']==3937==len(a['modules'])
 todo=['Aeneas'];seen=set()
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);n=a['modules'][m];todo+=n['imports']
  assert not m.startswith(('FS2.','AspisFormal.','AspisV8R19.','RawCut','R1Literal'))
  expected=snapshot['modules'][m]
  assert {k:v for k,v in n.items() if not k.startswith('resolved_')}==expected
  assert n['resolved_object_sha256']==n['objects']['.olean']['sha256']
 assert seen==set(a['modules'])
 audit=json.loads((E/'source-audit.json').read_text());assert len(audit['emitted_declarations'])==12
 assert sum(n['classification']=='SYNTHETIC_ROOT_WRAPPER' for n in audit['emitted_declarations'])==1
 assert sha(files['extraction/generated/translation.json'])==audit['raw_translation_sha256']
 print(json.dumps({'status':'PASS','archive_sha256':sha(archive.read_bytes()),'focused_targets':4,'axioms_reports':len(all_reports),'current_primitive_lemmas':8,'current_fresh_conditional_core_and_binding_lemmas':8,'Aeneas_only_import_modules':len(seen),'actual_Backend_build_ownership':'OPEN','current_literalMessage_custody':'OPEN'},sort_keys=True))
if __name__=='__main__':main()
