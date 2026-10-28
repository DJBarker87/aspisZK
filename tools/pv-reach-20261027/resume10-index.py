"""Derive all accounting and statement dispositions from retained exact receipts."""
import pathlib,json,subprocess,re,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10'
rs=[json.load(open(p)) for p in sorted(E.glob('receipt-[0-9]*.json'))];modules=[];index=[];failures=[]
for r in rs:
 a=r['attempt'];tim=(E/f'time-{a}.log').read_text();wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.*)',tim);peak=re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim);swaps=re.search(r'Swaps: (\d+)',tim)
 index.append(dict(attempt=a,accepted=r['accepted'],targets=[m['module'] for m in r['modules']],source_revision=r['source_revision'],scope_wall=wall[1] if wall else None,peak_rss_kib=int(peak[1]) if peak else None,swaps=int(swaps[1]) if swaps else None,aggregate_rss_peak_bytes=r['aggregate_rss_peak_bytes'],cgroup_memory_peak_bytes=r['cgroup_memory_peak_bytes'],swap_peak_bytes=r['swap_peak_bytes'],receipt=f'receipt-{a}.json'))
 for m in r['modules']:
  modules.append(dict(attempt=a,module=m['module'],accepted=m.get('accepted'),source=m['source'],object_sha256=m.get('object_sha256'),axioms=m.get('axioms'),exit=m.get('exit'),wall_seconds=m.get('wall_seconds'),peak_rss_kib=m.get('peak_rss_kib'),swaps=m.get('swaps'),deps_fingerprint=m.get('deps_fingerprint')))
  if not m.get('accepted'):failures.append(dict(attempt=a,module=m['module'],source=m['source'],output=m.get('output'),credit=False,unchanged_source_retained=True))
for name,content in [('receipt-index.json',index),('module-index.json',modules),('failures.json',failures)]: (E/name).write_text(json.dumps(content,indent=2)+'\n')
used=sorted(int(p.stem.split('-')[-1]) for p in E.glob('used-*.json'))
tally=dict(charged_attempts=len(rs),accepted_attempts=sum(r['accepted'] for r in rs),failed_attempts=sum(not r['accepted'] for r in rs),lean_processes=sum(len(r['modules']) for r in rs),kani=0,budget=100,used_ids=used,reserved_audit_ids=[40497,40498,40499],scope='six authorized chunks, otherwise one module per attempt',maximum_scope_rss_kib=max((r['peak_rss_kib'] or 0 for r in index),default=0),maximum_aggregate_rss_bytes=max((r['aggregate_rss_peak_bytes'] for r in index),default=0),maximum_swap_bytes=max((r['swap_peak_bytes'] for r in index),default=0))
(E/'TALLY.json').write_text(json.dumps(tally,indent=2)+'\n')
# Neither failed nor uncompiled candidates are admitted to the proof manifest.
added=subprocess.check_output(['git','diff','--diff-filter=A','--name-only','df48db9f6c','HEAD','--','docs/research/v8-r0-zk-20261009/lean/R1Z'],text=True).splitlines();by={m['source']['path']:m for m in modules};dis=[]
for p in added:
 if not p.endswith('.lean'):continue
 m=by.get(p);s=(R/p).read_bytes();dis.append(dict(path=p,sha256=hashlib.sha256(s).hexdigest(),disposition='accepted' if m and m['accepted'] else 'failed; retained without credit' if m else 'uncompiled draft; no credit',attempt=m['attempt'] if m else None))
(E/'candidate-dispositions.json').write_text(json.dumps(dis,indent=2)+'\n')
print(json.dumps(tally,indent=2))
