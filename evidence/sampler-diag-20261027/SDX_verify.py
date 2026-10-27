from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('SDX_[LR][0-9][0-9][0-9]/receipt.json'))]
errors=[];latest={}
for r in receipts:
 a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
 if not ad['allowed']:errors.append(a+' not admitted')
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+' wrong limits')
 if str(r['swaps'])!='0':errors.append(a+' swapped')
 for f,h in r['source_hashes'].items():
  if sha(E/a/'sources'/f)!=h:errors.append(a+' source hash '+f)
 if r['kind']=='lean' and r['exit_status']==0:
  latest[r['module']]=r
  for line in r['print_axioms']:
   if 'sorryAx' in line:errors.append(a+' unaccepted axiom')
for m,r in latest.items():
 src=E/(m+'.lean')
 if sha(src)!=r['source_hashes'][r['sources'][0]]:errors.append(m+' final source differs')
for x in json.loads((E/'SDX_kit_manifest.json').read_text()):
 p=Path(x['source']);q=Path(x['private'])
 if sha(p)!=x['sha256'] or sha(q)!=x['private_sha256']:errors.append('kit source pin')
 if q.read_text().replace('SDX_Join','XRn_Join')!=p.read_text():errors.append('non-name kit change')
for p in E.glob('*.lean'):
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()):errors.append(p.name+' forbidden source token')
lock=json.loads((E/'SDX_lock.json').read_text());graph=json.loads((E/'SDX_graph.json').read_text());location=json.loads((E/'SDX_loss_location.json').read_text())
if not (lock['unchanged'] and lock['before']==lock['after']==graph['lock_sha256']):errors.append('lock')
if graph['sampler_original_sha256']!=location['frozen_sampler_sha256']:errors.append('native sampler source not frozen')
paths=subprocess.check_output(['git','diff','--name-only','2996a93f560c5edbb5b056c054766d6f8c660cc8'],text=True).splitlines()
if any(not x.startswith('evidence/sampler-diag-20261027/') for x in paths):errors.append('outside job directory')
(E/'SDX_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
lean=[r for r in receipts if r['kind']=='lean'];rust=[r for r in receipts if r['kind']=='rust']
summary={'errors':errors,'lean_attempts':len(lean),'lean_pass':sum(r['exit_status']==0 for r in lean),'rust_runs':len(rust),'rust_pass':sum(r['exit_status']==0 for r in rust),'kani_runs':0,'lean_wall_seconds':sum(r['wall_seconds'] for r in lean),'lean_peak_rss_kib':max(int(r['peak_rss_kib']) for r in lean),'swap':0,'accepted_modules':list(latest),'final_audit':'SDX_L033','native_pass':'SDX_R003','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'admission':'allowed=true in each reservation; exit=0 enforced by SDX_attempt.py and native invocation transcript','result_scope':'diagnostic only; no premise removed'}
(E/'SDX_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
if errors:raise SystemExit(1)
