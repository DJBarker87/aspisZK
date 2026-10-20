#!/usr/bin/env python3
"""Collect focused check receipts, direct-import object pins and axiom audits."""
from pathlib import Path
import json,re,hashlib,subprocess
here=Path(__file__).resolve().parent;base=here.parents[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
rows=[]
for d in sorted(here.iterdir()):
 if not d.is_dir() or not (d/'receipt.json').exists():continue
 r=json.loads((d/'receipt.json').read_text());cmd=json.loads((d/'command.json').read_text())
 src=Path(cmd['argv'][-1]);paths=cmd['env']['LEAN_PATH'].split(':')
 imports=[]
 for mod in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):
  p=next((Path(root)/(mod.replace('.','/')+'.olean') for root in paths if (Path(root)/(mod.replace('.','/')+'.olean')).is_file()),None)
  imports.append({'module':mod,'object':str(p) if p else None,'sha256':sha(p) if p else None,'size':p.stat().st_size if p else None})
 fp=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
 log=(d/'lean.log').read_text() if (d/'lean.log').exists() else ''
 tim=(d/'time.log').read_text() if (d/'time.log').exists() else ''
 audits=[{'theorem':name,'axioms':[x.strip() for x in ax.split(',') if x.strip()]} for name,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log)]
 peak=re.search(r'(\d+)\s+maximum resident set size',tim);swaps=re.search(r'(\d+)\s+swaps',tim)
 r.update(deps_fingerprint=fp,direct_imports=imports,dependency_capture='postflight direct-import artifact snapshot; search path/compile input hashes retained per attempt',peak_rss_bytes=int(peak[1]) if peak else None,swaps=int(swaps[1]) if swaps else None,axioms=audits)
 if r.get('exit_status')==0:
  assert audits and all(set(a['axioms']) <= {'propext','Classical.choice','Quot.sound'} for a in audits),d
 if r['source_sha256']==sha(src):r['source_content_revision']=revision
 (d/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
 rows.append({'attempt':d.name,'module':r.get('module',src.stem),'exit_status':r['exit_status'],'source_sha256':r['source_sha256'],'source_revision':r['source_revision'],'deps_fingerprint':fp,'wall_seconds':r.get('wall_seconds'),'peak_rss_bytes':r['peak_rss_bytes'],'swaps':r['swaps'],'axioms':audits,'receipt':str(d.relative_to(here)/'receipt.json')})
final={}
for r in rows:
 src=base/'lean'/(r['module']+'.lean')
 if r['exit_status']==0 and src.exists() and r['source_sha256']==sha(src):final[r['module']]=r['attempt']
manifest={'schema':'focused-extractor-proof-packet-v1','job':'sampler-rows-25-32-20261020','branch':subprocess.check_output(['git','branch','--show-current'],text=True).strip(),'base_revision':rows[0]['source_revision'],'source_content_revision':revision,'scope':'conditional local source/literal row laws and R18 mapped-public formats; no full manifest replay','final_successes':final,'attempts':rows,'sources':{str(p.relative_to(base)):sha(p) for p in sorted((base/'lean').glob('RawSamplerSuffix*.lean'))},'pin':{'c16_funs_sha256':sha(base/'lean/extracted-public-preparation-c16-20261019/AspisR1PublicPreparation/Funs.lean')}}
p=base/'lean/RawDeployedTranscriptFormat.lean';manifest['sources'][str(p.relative_to(base))]=sha(p)
(here/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(final,indent=2))
