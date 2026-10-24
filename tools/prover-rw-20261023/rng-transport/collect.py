"""Collect only this preflight; retain previous ledgers and launch budget."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-transport'
H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023'
subprocess.run(['rsync','-a','--exclude=*.olean','dombarker@100.108.41.90:'+H+'/rng-transport/',str(E)+'/'],check=True)
# lean.py retained under tools, not duplicated evidence.
(E/'lean.py').unlink(missing_ok=True)
env=json.loads((E.parent/'rng-caller/env-J.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());assert 11551<=r['attempt']<=11559
 source=R/'docs/research/v8-r0-zk-20261009/lean'/(r['module']+'.lean')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
 r['effective_lean_command']=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+r['module']+'.olean',r['source_path']]
 r['effective_lean_path']=J+'/objects:'+env['LEAN_PATH']
 t=r['time_log'];r['wall_time']=re.search(r'Elapsed.*: (\S+)',t)[1];r['peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1]);r['swaps']=int(re.search(r'Swaps: (\d+)',t)[1])
 r['revision_assessment']='Exact parent revision plus immutable source and dependency hashes. Audit source was uncommitted at launch; final committed source hash matches receipt.' if r['attempt']==11552 else 'Exact committed theorem source revision; dependency objects reused with recorded hashes.'
 assert r['exit_status']==0 and len(r['print_axioms'])==4
 assert all(set(a.split('[',1)[1].split(']',1)[0].replace(' ', '').replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound'} for a in r['print_axioms'])
 p.write_text(json.dumps(r,indent=2)+'\n');rows.append(r)
prior=E.parent/'rng-material/ledger.json';old=json.loads(prior.read_text());assert old['cumulative_used']==211
ledger=dict(prior_ledger_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),prior_cumulative=211,cumulative_ceiling=220,remaining_at_entry=9,attempts=[r['attempt'] for r in rows],used=len(rows),cumulative_used=211+len(rows),remaining=9-len(rows),kani_used=44,kani_ceiling=60,kani_remaining=16)
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
refs=['rng-caller/rng-caller-aeneas-003/receipt.json','rng-caller/rng-caller-aeneas-003/stderr.log','rng-caller/11459-receipt.json','rng-native/11523-receipt.json','rng-material/11550-receipt.json']
(E/'reuse.json').write_text(json.dumps([dict(path=n,sha256=hashlib.sha256((E.parent/n).read_bytes()).hexdigest(),assessment='Historical source/control/failure evidence only; not a new native identity gate or replay') for n in refs],indent=2)+'\n')
for p in E.rglob('*.json'):
 assert p.stat().st_size<=5_000_000,(p,p.stat().st_size)
print(json.dumps(ledger))
