from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=obj(E/'NFI_AUDIT_ROOTS.json')['roots'];results=[];scopes=[];standard={'propext','Classical.choice','Quot.sound'}
for i in range(28,51):
 a=f'NFI_L{i:03}';r=obj(E/a/'receipt.json');assert r['exit_status']==0
 log=(E/a/'stdout.log').read_text();found=[json.loads(l[11:]) for l in log.splitlines() if l.startswith('NEP_RESULT ')]
 assert found
 printed=[l for l in log.splitlines() if 'depends on axioms:' in l or 'does not depend on any axioms' in l]
 for item in found:
  assert item['equal'] and set(item['collect_axioms'])==set(item['walked_axioms'])<=standard
  name='NEP_'+r['module']+'_'+item['root']+'_REACHABLE.txt';p=E/(name+'.xz');data=lzma.decompress(p.read_bytes());h=hashlib.sha256(data).hexdigest()
  assert (E/(name+'.sha256')).read_text().split()[0]==h
  results.append({**item,'attempt':a,'graph_archive':p.name,'uncompressed_sha256':h,'compressed_sha256':sha(p)})
 scopes.append(dict(attempt=a,module=r['module'],source_revision=r['source_revision'],exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],print_axioms=printed))
assert sorted(r['root'] for r in results)==sorted(roots) and len(results)==75
scan=[json.loads(s) for s in (E/'NFI_LOADED_scan.jsonl').read_text().splitlines()]
assert all(r['imports_match'] and not r['dangling'] for r in scan)
fixtures=[json.loads(l[11:]) for l in (E/'NFI_L026/stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
assert all(len(r['walked_axioms'])==1 for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
source=(E/'NFI_Driver.lean').read_text();baseline=Path('evidence/slice-q-mul7-20261104/NFF_Driver.lean').read_text();extract=lambda s:s[s.index('def referenceNames'):s.index('/-- Standalone runtime')]
assert extract(source)==extract(baseline)
link=obj(E/'NFI_L025/receipt.json');prior=obj(Path('evidence/slice-q-mul7-20261104/NFF_L044/receipt.json'))
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:assert link['source_hashes']['NFI_native/'+name]==prior['source_hashes']['NFF_native/'+name]
last=obj(E/'NFI_L027/receipt.json');all_rows=[json.loads(l) for l in (E/'NFI_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(all_rows)==150 and len({r['attempt'] for r in all_rows})==150
assert len([r for r in all_rows if r['kind']=='kani'])==100
for r in all_rows:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert obj(E/(r['attempt']+'-admission.json'))['exit']==0 and obj(E/(r['attempt']+'-admission.json'))['reservation']['allowed'] is True
assert (E.parent/'slice-q-mul4-20261104/NFA_WALKER.lean').read_bytes()==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
out=dict(status='PASS_COMBINED_HEADLINE_NFI',headline='AspisR1.RPx_Deployed.deployed',combined_attempt='NFI_L023',driver_source_sha256=sha(E/'NFI_Driver.lean'),driver_binary=obj(E/'NFI_L025/NFI_Driver_BINARY_PIN.json'),walker_unchanged=True,walker_C_sha256=link['source_hashes']['NFI_native/NFA_WALKER.c'],scanner_unchanged=True,scanner_sha256=hashlib.sha256(extract(source).encode()).hexdigest(),fixture_attempt='NFI_L026',fixtures=fixtures,roots=75,raw_graphs_equal_collectAxioms=True,standard_axioms_only=True,zero_unresolved_constants=True,incoherence_scan=dict(attempt='NFI_L027',modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=0,import_mismatches=0,output_sha256=sha(E/'NFI_LOADED_scan.jsonl'),exit_status=0,wall_seconds=last['wall_seconds'],peak_rss_kib=last['peak_rss_kib'],swaps=last['swaps']),scopes=scopes,results=results,sibling_excluded='NFF_L032 duplicate Phase owner; source-only NFB validator passes separately',budget=dict(kani=100,lean_audit=50,extraction=0,limits=dict(kani=100,lean_audit=50,extraction=5)),newly_closed=[])
(E/'NFI_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
c=obj(E/'NFI_CLOSED.json');c['headline_join']='PASS: NFI_L023 combined import; NFI_L027 incoherence scan; NFI_L028–050 raw ax2 audits';(E/'NFI_CLOSED.json').write_text(json.dumps(c,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','roots','incoherence_scan','budget']}))
