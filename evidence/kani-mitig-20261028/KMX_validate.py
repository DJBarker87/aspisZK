from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
rows=[]
for cfg in sorted(E.glob('KMX_[KRL][0-9][0-9][0-9].json')):
 a=cfg.stem;receipt=E/a/'receipt.json'
 if not receipt.exists():
  assert a=='KMX_K004',a
  rows.append(dict(attempt=a,result='pre-Kani input failure; no terminal receipt'));continue
 r=json.loads(receipt.read_text());ad=json.loads((E/(a+'-reservation.json')).read_text());assert ad['allowed'] is True,a
 assert r['swaps']=='0',(a,r['swaps'])
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert r['source_revision'],a
 assert r['source_hashes'].get('KMX_src/Cargo.lock',lock)==lock,a
 if r['kind'] in ['kani','rust'] and (E/(a+'-graph.json')).exists():
  g=json.loads((E/(a+'-graph.json')).read_text());assert g['allowed'] and not g['new_packages'] and not g['edge_errors'],a
  assert g['lock_before']==lock,a
  if r['exit_status']!=124:assert g.get('lock_after')==lock and g.get('unchanged'),a
 if r['kind']=='lean' and r['exit_status']==0:
  t=(E/a/'stdout.log').read_text();assert '#print axioms' not in t or 'sorryAx' not in t
  assert 'sorryAx' not in t,a
 rows.append({k:r.get(k) for k in ['attempt','kind','command','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','swaps','source_revision','source_hashes','print_axioms']})
assert sum(p['kind']=='kani' for p in [json.loads(x.read_text()) for x in E.glob('KMX_[KRL][0-9][0-9][0-9].json')])<=80
patch=(E/'KMX_copy_stubs.patch').read_text()
for name,path in [('KMX_stubs.rs',E/'KMX_stubs.rs.txt'),('KMX_native.rs',E/'KMX_native.rs.txt'),('KMX_CopyMeaning.lean',E.parents[1]/'lean/KMX_CopyMeaning.lean')]:
 part=next(part for part in patch.split('diff --git ') if part.startswith('a/'+name+' '))
 actual='\n'.join(l[1:] for l in part.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n'
 assert actual==path.read_text(),name
assert all(x['body_unchanged_except_namespace'] for x in json.loads((E/'KMX_REPLAY_BODY_AUDIT.json').read_text()))
(E/'KMX_LEDGER.json').write_text(json.dumps(rows,indent=2)+'\n')
print('KMX packet validation PASS:',len(rows),'attempts; K004 explicitly unresolved; K006 outer-timeout after-hash absent')
