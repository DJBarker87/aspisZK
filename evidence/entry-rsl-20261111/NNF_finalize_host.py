"""Bounded read-only pinning and own-workspace export. No cache deletion."""
from pathlib import Path
import hashlib,json,lzma,shutil,sys
B=Path.cwd()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda n,x:(B/n).write_text(json.dumps(x,indent=1)+'\n')
env=json.loads((B/'NNF_ENV.json').read_text());roots=env['LEAN_PATH'].split(':')
raw=lzma.decompress((B/'NNF_PIN_SELECTION.json.xz').read_bytes());h=hashlib.sha256(raw).hexdigest()
assert h==(B/'NNF_PIN_SELECTION.json.sha256').read_text().strip()
selection=json.loads(raw);selected=selection['selected'];n=len(selected)
for i in range(3):
 x=json.loads((B/f'NNF_PIN_BATCH_{i}.json').read_text())
 assert x['verified'] and x['selection_sha256']==h and x['start']==n*i//3 and x['end']==n*(i+1)//3 and x['total']==n
selected_paths={v['path']:v for v in selected.values()}
# The actual Aeneas objects resolved by every focused compiler remain pinned.
receipts=[]
for d in sorted(B.glob('NNF_L[0-9][0-9][0-9]')):
 if d.name==sys.argv[1]:continue
 rc=json.loads((d/'receipt.json').read_text());receipts.append(rc)
 for obj in rc['deps_fingerprint'].get('selected_objects',{}).values():
  p=Path(obj['path']);assert sha(p)==obj['sha256'],('INPUT OBJECT DRIFT',str(p))
  if '/Aeneas' in str(p):
   assert str(p) in selected_paths,('UNPINNED AENEAS PATH',str(p))
   assert selected_paths[str(p)]['sha256']==obj['sha256'],('AENEAS RESOLUTION DRIFT',str(p))
 for name,h in rc['source_hashes'].items():
  assert sha(d/'sources'/name)==h,('SNAPSHOT DRIFT',str(d),name)
seed=json.loads((B/'NNF_SEED_EXPECTED.json').read_text())
for x in seed:
 assert sha(Path(x['destination']))==x['sha256'],('IMPORTED SEED DRIFT',x['destination'])
archive={'inventory':'exact predecessor first-hit module inventory plus own/RSL additions; all rehashed in three bounded batches','LEAN_PATH':':'.join(roots),'selected':selected}
raw=json.dumps(archive,sort_keys=True).encode()
(B/'NNF_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NNF_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
export=B/'NNF_exports_20261111';export.mkdir(exist_ok=True);out=[]
modules=['NNF_Carrier','NNF_Dispatch','NNF_Reify','NNF_Folds','NNF_TAS','NNF_COMBINED_IMPORT','TCK_WeakRoot0','TAS_Interfaces']
for name in modules:
 rc=next(r for r in reversed(receipts) if r['module']==name)
 assert rc['exit_status']==0,(name,'latest receipt is not green')
 src='NNF_generated/'+name+'.lean'
 assert sha(B/src)==rc['source_hashes'][src],('STALE EXPORT SOURCE',name)
 for f in (B/'NNF_objects').glob(name+'.*'):
  if f.suffix not in ['.olean','.private','.server','.ir']:continue
  dst=export/f.name
  if dst.exists():assert sha(dst)==sha(f),('EXPORT DRIFT',str(dst))
  else:shutil.copy2(f,dst)
  out.append({'module':name,'path':str(dst),'sha256':sha(dst),'bytes':dst.stat().st_size,'source_sha256':rc['source_hashes'][src],'receipt':rc['attempt']})
write('NNF_EXPORT.json',{'path':str(export),'prepend_to':'NNF_ENV.json LEAN_PATH','modules':out,'inherited_seed_retained':str(B/'NNF_seed'),'cold_release_replay':False})
# Retain all optimized audit C inputs, including unchanged canonical walker.
inputs=B/'NNF_AUDIT_INPUTS';inputs.mkdir(exist_ok=True);cpins=[]
for f in sorted((B/'NNF_native').glob('*.c')):
 raw=f.read_bytes();(inputs/(f.name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(inputs/(f.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 cpins.append({'path':str(f),'sha256':sha(f),'bytes':len(raw),'archive':str(inputs/(f.name+'.xz'))})
write('NNF_TOOL_PINS.json',{'audit_C':cpins,'audit_binary':{'path':str(B/'NNF_native/NNF_ProofDriver'),'sha256':sha(B/'NNF_native/NNF_ProofDriver')},'runner':{'path':str(B/'S2W_run_host.py'),'sha256':sha(B/'S2W_run_host.py')},'Aeneas_objects':sum(n.startswith(('Aeneas.','Aeneas/','AeneasMeta.','AeneasMeta/')) for n in selected)})
write('NNF_RETENTION.json',{'available_objects_rehashed':len(selected),'completed_receipts_verified':len(receipts),'host_free_bytes':shutil.disk_usage(B).free,'workspace_bytes':sum(p.stat().st_size for p in B.rglob('*') if p.is_file()),'seed_files_verified':len(seed),'deletions':0,'own_workspace_retained':str(B),'all_source_snapshots_match':True,'all_direct_dependency_pins_match':True})
print(json.dumps({'objects':len(selected),'exports':len(out),'receipts':len(receipts),'audit_C':len(cpins)}))
