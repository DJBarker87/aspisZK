"""Additive empty-delta validation; preserves historical corpus refusal."""
from pathlib import Path
import sys,json,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent;ROOT=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(E.parent/'native-ledger3-20261029'))
import NDT_validate
base=json.loads((E.parent/'native-ledger3-20261029/NDT_LEDGER.json').read_text())
NDT_validate.validate_invariants(base)
ledger=E.parent/'inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz'
ngb=json.loads(lzma.decompress(ledger.read_bytes()))
delta=json.loads((E/'NGG_LEDGER_DELTA.json').read_text());closed=json.loads((E/'NGG_CLOSED.json').read_text())
assert delta['rows']==closed['composed_rows']==[] and delta['status']==closed['status']=='OPEN'
rows=[json.loads(l) for l in (E/'NGG_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
counts={k:sum((r['kind'] not in ['kani','extract']) if k=='lean' else r['kind']==k for r in rows) for k in ['kani','lean','extract']}
assert all(counts[k]<=n for k,n in dict(kani=120,lean=60,extract=2).items())
verdicts=[];checked=0
for row in rows:
 a=row['attempt'];receipt=E/a/'receipt.json'
 if a=='NGG_K018':
  assert not receipt.exists() and (E/'NGG_K018-STOP.json').exists();continue
 d=json.loads(receipt.read_text());assert d['limits']==expected,(a,d['limits'])
 assert d['swaps']=='0',a
 assert all(k in d for k in ['module','source_revision','exit_status','wall_seconds','peak_rss_kib','source_hashes','print_axioms'])
 checked+=1
 if d['kind']=='kani':
  graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text())
  assert graph['graph_matches_frozen'] and graph['exact_LPm_graph'],a
  assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  assert not json.loads((E/(a+'-source-check.json')).read_text())['errors'],a
  assert json.loads((E/(a+'-rule16-check.json')).read_text())['no_writable_static'],a
  assert d['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
  assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
  log=(E/a/'stdout.log').read_text();verdicts.append(dict(attempt=a,success=d['exit_status']==0,timeout='CBMC timed out.' in log,failed_checks=[l.strip() for l in log.splitlines() if 'Failed Checks:' in l]))
(E/'NGG_NATIVE_VERDICTS.json').write_text(json.dumps(verdicts,indent=1)+'\n')
# Frozen shipped tree and current worktree must be unchanged; no rebuild claim.
for args in [['diff','--exit-code','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs','Cargo.lock'],['diff','--exit-code','--','crates','programs','Cargo.lock']]:
 assert subprocess.run(['git',*args],cwd=ROOT,capture_output=True).returncode==0
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file())
out=dict(status='PASS additive empty delta only',historical_invariants=True,historical_full_cli_refusal_preserved=True,ledger_base_sha256=sha(ledger.read_bytes()),ledger_base_rows=len(ngb['rows']),changed_ledger_rows=0,counts=counts,receipts_checked=checked,unreceipted_stopped_attempt='NGG_K018',composed_rows=0,shipped_files_changed=False,negative_controls_require_semantic_review=True,production_status='B/D OPEN; no native composed credit')
(E/'NGG_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
