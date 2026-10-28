"""Receipt/source checks only; no proof launch."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;rows=[]
for p in sorted(E.glob('NBC_[KL]*/receipt.json')):
 r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert json.loads((E/(r['attempt']+'-reservation.json')).read_text())['allowed'] is True
 assert r['swaps']=='0'
 if r['kind']=='kani':
  assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log
  assert json.loads((E/(r['attempt']+'-graph-check.json')).read_text())['graph_matches_frozen']
  for end in ['before','after']:assert (E/(r['attempt']+'-lock-'+end+'.log')).read_text().strip()=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 elif r['exit_status']==0:
  assert r['print_axioms'] and 'error:' not in log
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^]]*)\]',line)
   if m:assert set(x.strip() for x in m[1].split(','))<=set(['propext','Classical.choice','Quot.sound'])
 rows.append({k:r[k] for k in ['attempt','kind','module','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms'] if k in r})
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani']
assert len(lean)<=100 and len(kani)<=30
for mod,a in [('NBC_ReleaseLeaves','NBC_L002'),('NBC_Filled','NBC_L004'),('NBC_Audit','NBC_L005')]:
 r=next(r for r in rows if r['attempt']==a);assert r['exit_status']==0
 assert hashlib.sha256(Path('lean',mod+'.lean').read_bytes()).hexdigest()==r['source_hashes']['NBC_generated/'+mod+'.lean']
for p in Path('lean').glob('NBC_*.lean'):assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|maxHeartbeats|maxRecDepth',p.read_text(),re.M)
subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs'],check=True)
subprocess.run(['git','diff','--check'],check=True)
out=dict(lean_used=len(lean),lean_limit=100,kani_used=len(kani),kani_limit=30,lean_passed=[r['attempt'] for r in lean if r['exit_status']==0],lean_rejected=[r['attempt'] for r in lean if r['exit_status']!=0],kani_passed=[r['attempt'] for r in kani],max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),total_prover_wall_seconds=sum(r['wall_seconds'] for r in rows),all_swaps_zero=True,timeouts=[],memory_kills=[],shipped_crates_programs_unchanged=True,headline_premises_removed=0,unit_status=dict(U00='OPEN: filled, SolanaDigest::digest, error',U01='OPEN: held behind U00',U02='OPEN: held behind U00 and U01'),attempts=rows)
(E/'NBC_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='attempts'},indent=2))
