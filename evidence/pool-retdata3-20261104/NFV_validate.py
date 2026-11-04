"""Lane evidence validation: raw terminal receipts, immutable lock and caps."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NFV_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
counts={'kani':0,'lean':0,'extract':0};checks=[]
for row in rows:
 a=row['attempt'];r=json.loads((E/a/'receipt.json').read_text());kind='kani' if row['kind']=='kani' else 'extract' if row['kind']=='extract' else 'lean';counts[kind]+=1
 assert row['exit_status']==r['exit_status']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert str(r['swaps'])=='0',a
 assert all(k in r for k in ['wall_seconds','peak_rss_kib','source_revision','source_hashes']),a
 adm=json.loads((E/(a+'-admission.json')).read_text());assert adm['exit']==0 and adm['reservation']['allowed'] is True,a
 if kind=='kani':
  graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());rule=json.loads((E/(a+'-rule16-check.json')).read_text());features=json.loads((E/(a+'-metadata-pin.json')).read_text())
  assert graph['graph_matches_frozen'] and graph['exact_LPm_graph'],a
  assert rule['no_writable_static'],a
  assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
  assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  crates={p['name']:p['features'] for p in features['features_all_crates']}
  assert {'r1-split-checkpoint','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit'}<=set(crates['aspis-pool']) and 'no-entrypoint' not in crates['aspis-pool'],a
  assert 'pool-v1-kernel' in crates['aspis-statement'],a
  out=(E/a/'stdout.log').read_text();checks.append(dict(attempt=a,exit=r['exit_status'],timeout='timed out' in out.lower(),unwind='unwinding assertion' in out))
assert counts['kani']<=80 and counts['lean']<=50 and counts['extract']<=1
for p in E.glob('NFV_*.lean'):
 assert not re.search(r'\b(?:sorry|admit|axiom)\b',re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)),p
assert not any(p.is_file() and p.stat().st_size>20000000 for p in E.rglob('*'))
(E/'NFV_VALIDATION.json').write_text(json.dumps(dict(counts=counts,limits=dict(kani=80,lean=50,extract=1),admission_caps_swap_graph_lock_features_rule16=True,terminal_native=checks,all_new_sources_no_admissions=True,shipped_files_changed=False),indent=1)+'\n')
print(counts,'validated')
