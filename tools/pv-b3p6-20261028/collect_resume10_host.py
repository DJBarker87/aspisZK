"""Archive this round's exact receipts, sources, and admission decisions."""
from pathlib import Path
import json,shutil,hashlib,re,datetime
from run import H
O=H/'archive-resume10';R=O/'receipts';R.mkdir(parents=True,exist_ok=True);rows=[];refusals=[];errors=[]
for p in sorted(H.glob('lean-640[0-9][0-9]*')):
 if not p.is_dir():continue
 dest=R/p.name;dest.mkdir(exist_ok=True)
 for f in p.rglob('*'):
  if not f.is_file()or f.suffix in ['.olean','.ilean']:continue
  q=dest/f.relative_to(p);q.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(f,q)
 rp=p/'receipt/receipt.json'
 if not rp.exists():
  if (p/'refusal.json').exists():refusals.append(dict(label=p.name,**json.loads((p/'refusal.json').read_text())))
  elif (p/'barrier.json').exists()and json.loads((p/'barrier.json').read_text()).get('allowed')is not True:refusals.append(dict(label=p.name,exit=78,charged_lean_attempts=0,compiler_started=False))
  continue
 x=json.loads(rp.read_text());log=(rp.parent/'stdout.log').read_text()+'\n'+(rp.parent/'stderr.log').read_text()
 axioms=[m[0]for m in re.finditer(r"^'([^'\n]+)' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",log,re.M)]
 x['print_axioms']=axioms
 for gate in ['reservation.json','barrier.json']:
  if not (p/gate).exists()or json.loads((p/gate).read_text()).get('allowed')is not True:errors.append(dict(label=p.name,gate=gate))
 sha=hashlib.sha256((p/'source.lean').read_bytes()).hexdigest()
 if sha!=x['source_sha256']:errors.append(dict(label=p.name,source_snapshot_mismatch=True))
 row=dict(label=p.name,module=x['module'],attempt=x['attempt'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],lean_source_revision=x['lean_source_revision'],source_sha256=sha,print_axioms=axioms,receipt='receipts/'+p.name+'/receipt/receipt.json')
 rows.append(row);(dest/'receipt/receipt.json').write_text(json.dumps(x,indent=2)+'\n')
for name in ['TALLY-resume10.json','project-resolution-resume10.json','external-verification-resume10.json','cache-verification-resume10.json']:
 shutil.copy2(H/name,O/name)
for name,x in [('receipt-index.json',rows),('admission-audit.json',dict(errors=errors,refusals=refusals,void_attempts=[] if not errors else 'REVIEW REQUIRED'))]:
 (O/name).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(lean_attempts=len(rows),pass_count=sum(r['exit']==0 for r in rows),fail_count=sum(r['exit']!=0 for r in rows),errors=errors,refusals=refusals)))
