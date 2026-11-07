#!/usr/bin/env python3
"""Prepare owned frozen transport and explicit serial extraction attempts."""
from pathlib import Path
import subprocess,json,lzma,base64,hashlib,shutil
E=Path(__file__).resolve().parent;N=E.parent/'extract-stage-20261106';H='/home/dombarker/project-offloads/codex-cx-emission-repro-20261110'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(p,rev='HEAD'):return subprocess.check_output(['git','show',rev+':'+p])
def main():
 # Unchanged stager copied as a pinned evidence input, never patched.
 shutil.copy2(N/'NHR_stage.py',E/'NMH_NHR_stage.py')
 manifest=json.loads((N/'NHR_STAGING_MANIFEST.json').read_text());payload=json.loads(lzma.decompress((N/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()))
 pool='b936275465';listing=subprocess.check_output(['git','ls-tree','-rz',pool,'programs/aspis-pool']).split(b'\0')
 for p in list(payload):
  if p.startswith('programs/aspis-pool/'):del payload[p];del manifest['files'][p]
 for line in listing:
  if not line:continue
  meta,p=line.split(b'\t');mode,kind,oid=meta.decode().split();p=p.decode();assert kind=='blob';raw=git(p,pool)
  payload[p]=base64.b64encode(raw).decode();manifest['files'][p]=dict(bytes=len(raw),git_blob=oid,mode=mode,sha256=sha(raw),source_revision=pool)
 manifest['pool_amendment_revision']=subprocess.check_output(['git','rev-parse',pool],text=True).strip()
 raw=json.dumps(payload,sort_keys=True).encode();(E/'NMH_FROZEN_PAYLOAD.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NMH_FROZEN_PAYLOAD.json.sha256').write_text(sha(raw)+'\n');(E/'NMH_STAGING_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
 plan=json.loads((E/'NMH_PLAN.json').read_text());runs={}
 for g in plan['groups']:
  for c in g['configuration_candidates']:
   if not c['manifest']:continue
   # Native selectors must occur in frozen release; reference/outlined roots cannot be invented.
   if any(any(s in r for s in ['NGN_extraction_entry','NJT_claims_ref']) for r in c['roots']):continue
   cc=c['charon_command'];ac=c['aeneas_command'];key=json.dumps([cc[1:cc.index('--dest-file')],cc[cc.index('--manifest-path')+2:],ac[1:ac.index('-dest')]],sort_keys=True)
   if key not in runs:runs[key]=dict(configuration=c,groups=[],members=[],bytes=0)
   r=runs[key]
   if g['group'] not in r['groups']:r['groups'].append(g['group']);r['members']+=g['members'];r['bytes']+=g['bytes']
 ordered=sorted(runs.values(),key=lambda r:r['bytes'])
 for i,r in enumerate(ordered,1):
  r['run']='NMH_E%03d'%i;c=r['configuration'];cc=c['charon_command'].copy();ac=c['aeneas_command'].copy();out=H+'/'+r['run']+'_emitted';llbc=out+'/repro.llbc'
  cc[cc.index('--dest-file')+1]=llbc;cc[cc.index('--manifest-path')+1]=H+'/NMH_workspace/'+c['manifest']
  if '--locked' not in cc:cc.insert(cc.index('--offline'),'--locked')
  ac[ac.index('-dest')+1]=out+'/raw';ac[-1]=llbc
  r['charon_command']=cc;r['aeneas_command']=ac;r['opacity']=c['opacity'];r['basis']='Exact archived arrays, relocated only output/workspace paths; --locked strengthened where missing. Frozen source only, no outlined driver inserted.'
  (E/(r['run']+'_spec.json')).write_text(json.dumps(r,indent=2)+'\n')
 plan['runs']=ordered
 (E/'NMH_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
 print(json.dumps(dict(runs=len(ordered),group_members=sum(len(r['members']) for r in ordered),transport_files=len(payload),transport_bytes=sum(v['bytes'] for v in manifest['files'].values()))))
 for r in ordered:print(r['run'],r['groups'],r['configuration']['namespace'],r['configuration']['roots'])
if __name__=='__main__':main()
