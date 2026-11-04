from pathlib import Path
import json,hashlib,re,collections
E=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();obj=lambda p:json.loads(Path(p).read_text())
xs=[json.loads(s) for s in (E/'NFA_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(xs)==122 and len({x['attempt'] for x in xs})==122
assert sum(x['kind']=='kani' for x in xs)==22
assert sum(x['kind']!='kani' for x in xs)==100
m=obj(E/'NFA_FINAL_MANIFEST.json');r=obj(E/'NFA_L100/receipt.json');assert r['exit_status']==0
expected=[root for x in m['entries'] for root in x['roots']]
actual=[]
for line in r['print_axioms']:
 match=re.match("'([^']+)'",line);assert match;actual.append(match[1]);assert 'sorryAx' not in line
 if 'depends on axioms:' in line:
  axioms=line.split('[',1)[1].split(']',1)[0].split(', ');assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
assert actual==expected and len(actual)==35
for entry in m['entries']:
 p=E/(entry['module']+'.lean');assert sha(p)==entry['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom |set_option (?:maxRecDepth|maxHeartbeats)',p.read_text(),re.M)
for x in xs:
 assert obj(E/(x['attempt']+'-admission.json'))['exit']==0
 assert obj(E/(x['attempt']+'-admission.json'))['reservation']['allowed'] is True
 for name,h in x['source_hashes'].items():assert sha(E/x['attempt']/'sources'/name)==h,(x['attempt'],name)
a=obj(E/'NFA_AUDIT.json');assert a['standard_axioms_only'] and a['zero_unresolved_constants'] and a['unique_roots']==152
assert (E/'NFA_WALKER.lean').read_bytes()==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
assert obj(E/'NFA_NEW_REPLAY.json')['exit_status']==0
assert obj(E/'NFA_CLEANUP.json')['all_own_cgroups_terminal']
assert obj(E/'NFA_CLOSED.json')['newly_closed_by_NFA']==[]
assert obj(E/'NFA_EDGES.json')['newly_certified_edges']==[]
assert all(p.stat().st_size<=20*1024**2 for p in E.rglob('*') if p.is_file())
result=dict(status='PASS_SCOPED_COHERENT_NFA_FOREST',target=r['sources'][0],exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],cgroup_memory_peak_bytes=r['cgroup_memory_peak_bytes'],source_revision=r['source_revision'],source_tree_dirty=r['source_tree_dirty'],source_hashes=r['source_hashes'],print_axioms=r['print_axioms'],new_top_theorems=35,math_modules=17,full_frozen_release_replay=False,source_and_receipt_hashes_checked=True,budget_kind_counts=dict(collections.Counter(x['kind'] for x in xs)),new_NFA_rows_closed=0,security_target_established=False)
(E/'NFA_FINAL_MANIFEST_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
a['new_NFA_final_audit']=result;(E/'NFA_AUDIT.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','new_top_theorems','math_modules','budget_kind_counts','new_NFA_rows_closed']}))
