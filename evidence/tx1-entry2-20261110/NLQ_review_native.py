from pathlib import Path
import json,lzma,re
E=Path(__file__).resolve().parent
attempts=[json.loads(l) for l in (E/'NLQ_ATTEMPTS.jsonl').read_text().splitlines()]
rows=[]
for r in attempts:
 a=r['attempt']
 if not a.startswith('NLQ_K'):continue
 p=E/a/'stdout.log.xz'
 log=lzma.decompress(p.read_bytes()).decode() if p.exists() else (E/a/'stdout.log').read_text()
 cfg=json.loads((E/(a+'.json')).read_text())
 checks={}
 for kind in ['source','lock','graph']:
  p=E/(a+'-'+kind+'-check.json')
  checks[kind]=json.loads(p.read_text()) if p.exists()else None
 failed=[s for s in log.splitlines() if 'Failed Checks:' in s]
 rows.append(dict(attempt=a,module=r['module'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],limits=r.get('limits'),source_revision=r['source_revision'],CARGO_TARGET_DIR=cfg['env']['CARGO_TARGET_DIR'],offline=cfg['env'].get('CARGO_NET_OFFLINE'),rustflags=cfg['env'].get('RUSTFLAGS'),cbmc_timeout='CBMC timed out' in log,failed_checks=failed,pre_post_checks=checks,credit='NONE: diagnostic, qualified cut, fidelity control, or timeout; no row root'))
(E/'NLQ_NATIVE_REVIEW.json').write_text(json.dumps(dict(attempt_count=len(rows),rows=rows,target_established=False),indent=1)+'\n')
print(json.dumps(dict(native_runs=len(rows),timeouts=[r['attempt'] for r in rows if r['cbmc_timeout']],missing_checks=[r['attempt'] for r in rows if any(v is None for v in r['pre_post_checks'].values())])))
