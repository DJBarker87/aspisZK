from pathlib import Path
import json,re,hashlib,lzma,shutil
B=Path(__file__).resolve().parent
p=B.parent/'codex-pv-evhc2-20261029/resume3/COHORT-MANIFEST.json';shutil.copyfile(p,B/'COHORT-MANIFEST.json')
results={}
for a in [90000,90001]:
 d=B/f'lean-{a}';r=json.load(open(d/'receipt.json'));log=(d/'stdout.log').read_text()
 raw=[];errors=[]
 for line in log.splitlines():
  if 'NDP_RESULT ' in line:raw.append(json.loads(line.split('NDP_RESULT ',1)[1]))
  if 'error:' in line:errors.append(line)
 results[str(a)]={'module':r['module'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'source_revision':r['source_revision'],'limits':r['limits'],'cgroup_memory_peak_bytes':r['cgroup_memory_peak_bytes'],'print_axioms':r['print_axioms'],'raw_audit_results':raw,'raw_audit_errors':errors,'first_error':errors[0] if errors else None}
 (d/'full-print-axioms.txt').write_text('\n'.join(r['print_axioms'])+'\n')
obj=B.parent/'codex-pv-bridge-20261101/objects/PV_BR_FixtureConsumer.olean'
outputs=[]
for suffix in ['.olean','.olean.server','.olean.private','.ir']:
 p=obj.with_suffix(suffix)
 if p.exists():
  with p.open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
  outputs.append({'path':str(p),'sha256':h,'bytes':p.stat().st_size})
(B/'RESULTS.json').write_text(json.dumps({'runs':results,'compiled_outputs':outputs,'consumer_attempts':1,'audit_attempts':1,'raw_audit_complete':False,'fallback':'All 31 #print axioms queries completed in each run. Labelled #print axioms only; raw-walk coverage incomplete, no extra launch.'},indent=2)+'\n')
# Preserve every large input/output, compressed with a hash of its full original.
for p in sorted(B.rglob('*')):
 if p.is_file() and p.stat().st_size>20*1024*1024 and p.suffix!='.xz':
  with p.open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
  p.with_name(p.name+'.sha256').write_text(h+'  '+p.name+'\n')
  with p.open('rb') as src,lzma.open(str(p)+'.xz','wb',preset=6) as out:shutil.copyfileobj(src,out)
files=[]
for p in sorted(B.rglob('*')):
 if not p.is_file() or p.stat().st_size>20*1024*1024:continue
 if p.name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:continue
 files.append(str(p.relative_to(B)))
(B/'COLLECT-FILES.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps({a:{k:v for k,v in r.items() if k not in ['print_axioms','raw_audit_results','raw_audit_errors','limits']}|{'raw_results':len(r['raw_audit_results']),'errors':r['raw_audit_errors']} for a,r in results.items()},indent=2),flush=True)
print('FILES',len(files),flush=True)
