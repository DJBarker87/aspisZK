"""Read-only receipt/current-source audit; launches no prover."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NBR_[LK]*/receipt.json')):
 r=json.loads(p.read_text())
 required=['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits','deps_fingerprint']
 assert all(k in r for k in required),(p,'missing fields')
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text());assert ad['allowed'] is True
 if a.startswith('NBR_K'):
  g=json.loads((E/(a+'-graph-check.json')).read_text())
  lp=E/(a+'-lock-check.json')
  if lp.exists():lock=json.loads(lp.read_text())
  else:
   after=(E/(a+'-lock-after.log')).read_text().split()[0]
   lock={'before':g['lock_sha256'],'after':after,'unchanged':after==g['lock_sha256']}
  assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors']
  assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 rows.append(r)
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani']
assert len(lean)<=100 and len(kani)==30
current={}
for p in sorted(Path('lean').glob('NBR_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[r for r in lean if r['module']==p.stem and r['exit_status']==0 and sha in r['source_hashes'].values()]
 assert matches,(p,'no matching accepted snapshot')
 current[str(p)]={'sha256':sha,'accepted_attempt':matches[-1]['attempt'],'axioms':matches[-1]['print_axioms']}
 assert not re.search(r'\b(sorry|admit|axiom)\b',p.read_text()),p
au=json.loads((E/'NBR_L046/receipt.json').read_text());assert au['exit_status']==0 and len(au['print_axioms'])==39
for s in au['print_axioms']:
 assert 'sorryAx' not in s
 if 'depends on axioms:' in s:
  assert set(s.split('[')[1].split(']')[0].split(', '))<={'propext','Classical.choice','Quot.sound'}
changed=subprocess.check_output(['git','diff','--name-only','0a709ba4e9e24b6b3887ecaf38fa8b36352eedf8'],text=True).splitlines()
assert all(n.startswith('evidence/native-prepare3-20261028/') or n.startswith('lean/NBR_') for n in changed),changed
out={'lean_compile_attempts':len(lean),'kani_configured_invocations':len(kani),'kani_match_failure_included':'NBR_K001','precompile_validation_stop_excluded':'NBR_L021','limits_verified':True,'frozen_graph_and_lock_each_kani':True,'current_sources':current,'accepted_axioms':au['print_axioms'],'changed_tracked_paths':changed,'receipts':rows}
(E/'NBR_LEDGER.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['lean_compile_attempts','kani_configured_invocations','limits_verified','frozen_graph_and_lock_each_kani']}))
