"""Archive this round's exact receipts, sources, and admission decisions."""
from pathlib import Path
import json,shutil,hashlib,re,datetime
from run import H
O=H/'archive-resume14';R=O/'receipts';R.mkdir(parents=True,exist_ok=True);rows=[];refusals=[];errors=[]
for p in sorted(H.glob('lean-694[0-9][0-9]*')):
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
for name in ['TALLY-resume14.json','project-resolution-resume14.json','external-verification-resume14.json','cache-verification-resume14.json']:
 shutil.copy2(H/name,O/name)
for name,x in [('receipt-index.json',rows),('admission-audit.json',dict(errors=errors,refusals=refusals,void_attempts=[] if not errors else 'REVIEW REQUIRED'))]:
 (O/name).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(lean_attempts=len(rows),pass_count=sum(r['exit']==0 for r in rows),fail_count=sum(r['exit']!=0 for r in rows),errors=errors,refusals=refusals)))


native=[]
for prefix in ['missing227-resume14-','matrix227-resume14-','equality227-resume14-','raw227-resume14-','d188227-resume14-']:
 for p in sorted(H.glob(prefix+'*')):
  if not p.is_dir():continue
  dest=R/p.name;dest.mkdir(exist_ok=True)
  for f in p.rglob('*'):
   if f.is_file():
    q=dest/f.relative_to(p);q.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(f,q)
  rp=p/'receipt/receipt.json'
  if rp.exists():
   r=json.loads(rp.read_text());r['label']=p.name;r['print_axioms']='N/A: extraction or finite native observation, not a theorem';native.append(r)
for p in H.glob('expanded227-resume14-*.json'):shutil.copy2(p,O/p.name)
for p in (H/'source-prepared-resume14').glob('*-*.json'):shutil.copy2(p,O/('source-prepared-'+p.name))
(O/'native-receipt-index.json').write_text(json.dumps(native,indent=2)+'\n')
assert len(native)<=30

# Small generation, harness, binary-hash and source-association records only.
for pat in ['*-resume14-*-inputs.json','*-resume14-*-binary.json','*-binding-resume14.json','d18813-*.json','range-source-resume14.json']:
 for p in H.glob(pat):
  if p.is_file():shutil.copy2(p,O/p.name)
for p in H.glob('missing-resume14-*'):
 if not p.is_dir():continue
 out=O/'extraction'/p.name.removeprefix('missing-resume14-');out.mkdir(parents=True,exist_ok=True)
 for f in p.glob('*.json'):shutil.copy2(f,out/f.name)
