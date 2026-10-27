"""Audit receipts and scope; this script does not launch a prover."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent; rows=[]
for f in sorted(E.glob('LPk_[KL]*/receipt.json')):
 r=json.loads(f.read_text());a=r['attempt'];log=(f.parent/'stdout.log').read_text()
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert json.loads((E/(a+'-reservation.json')).read_text())['allowed'] is True
 if r['kind']=='kani':
  assert json.loads((E/(a+'-graph-check.json')).read_text())['graph_matches_frozen']
  for end in ['before','after']:
   assert (E/(a+'-lock-'+end+'.log')).read_text().split()[0]=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  if r['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL' in log
 else:
  if r['exit_status']==0:
   assert r['print_axioms']
   for line in r['print_axioms']:
    m=re.search(r'axioms: \[([^]]*)\]',line)
    if m:assert set(x.strip() for x in m[1].split(','))<=set(['propext','Classical.choice','Quot.sound'])
 rows.append({k:r[k] for k in ['attempt','kind','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani']
assert len(lean)<=60 and len(kani)<=20
for module,a in [('LPk_Step','LPk_L003'),('LPk_Cohort','LPk_L004'),('LPk_Induction','LPk_L006'),('LPk_Result','LPk_L008'),('LPk_Modular','LPk_L009'),('LPk_Chunks','LPk_L011'),('LPk_Constant','LPk_L012'),('LPk_ReturnChecks','LPk_L013'),('LPk_Casts','LPk_L014')]:
 r=next(x for x in rows if x['attempt']==a)
 assert r['exit_status']==0
 assert hashlib.sha256((E/(module+'.lean')).read_bytes()).hexdigest()==r['source_hashes']['LPk_generated/'+module+'.lean']
for p in E.glob('LPk_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|maxHeartbeats|maxRecDepth',p.read_text(),re.M)
subprocess.run(['git','diff','--check'],check=True)
subprocess.run(['git','diff','--exit-code','1c2ce64719118a608dc234627ffe45d62fcbd104','--','crates','programs'],check=True,capture_output=True)
assert not json.loads((E/'LPk_SOURCE.json').read_text())['errors']
out={'lean_used':len(lean),'lean_limit':60,'kani_used':len(kani),'kani_limit':20,'metadata_only_preflight':'K001 excluded from Kani run count; conservatively identifiers consume a slot','lean_passed':[r['attempt'] for r in lean if r['exit_status']==0],'kani_passed':[r['attempt'] for r in kani if r['exit_status']==0],'timeouts':[r['attempt'] for r in rows if 'timed out' in (E/r['attempt']/'stdout.log').read_text()],'max_rss_kib':max(int(r['peak_rss_kib']) for r in rows),'total_wall_seconds':sum(r['wall_seconds'] for r in rows),'all_swaps_zero':all(str(r['swaps'])=='0' for r in rows),'shipped_crates_programs_unchanged':True,'attempts':rows}
(E/'LPk_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='attempts'},indent=2))
