from pathlib import Path
import json,hashlib,lzma,sys
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Attempt identifiers are explicit: never guess an unsubmitted or failed scope.
combined,link,scan,fixtures,*proofs=sys.argv[1:]
rs=[];scopes=[];standard={'propext','Classical.choice','Quot.sound'}
for a in proofs:
 r=obj(E/a/'receipt.json');assert r['exit_status']==0
 found=[json.loads(l[11:]) for l in (E/a/'stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
 assert found
 for x in found:
  assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=standard,x
  name='NEP_'+r['module']+'_'+x['root']+'_REACHABLE.txt';p=E/(name+'.xz');plain=lzma.decompress(p.read_bytes())
  assert (E/(name+'.sha256')).read_text().split()[0]==hashlib.sha256(plain).hexdigest()
  rs.append({**x,'attempt':a,'graph_archive':p.name,'archive_sha256':sha(p),'uncompressed_sha256':hashlib.sha256(plain).hexdigest()})
 scopes.append({k:r[k] for k in ['attempt','module','command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
assert sorted(x['root'] for x in rs)==sorted(obj(E/'NFN_AUDIT_ROOTS.json'))
loaded=[json.loads(l) for l in (E/'NFN_LOADED_scan.jsonl').read_text().splitlines()]
assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in loaded)
fx=[json.loads(l[11:]) for l in (E/fixtures/'stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
assert len(fx)==8 and all(x['equal'] for x in fx)
assert all(len(x['walked_axioms'])==1 for x in fx[:4]) and all(not x['walked_axioms'] for x in fx[4:])
c=obj(E/combined/'receipt.json');assert c['exit_status']==0
assert c['source_hashes']['NFN_generated/NFN_COMBINED_IMPORT.lean']==sha(E/'NFN_COMBINED_IMPORT.lean')
sr=obj(E/scan/'receipt.json');lr=obj(E/link/'receipt.json')
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 assert lr['source_hashes']['NFN_native/'+n]==sha(E/'NFN_native'/n)
base=(E.parent/'slice-q-mul7-20261104/NFF_Driver.lean').read_text();current=(E/'NFN_Driver.lean').read_text()
# The raw walker call and strict importAll/private setup are preserved.
assert 'importAll := true' in current and '(level := .private)' in current
assert base[base.index('  let ctx : Command.Context'):]==current[current.index('  let ctx : Command.Context'):]
assert obj(E/'NFN_WALKER_IDENTITY.json')['byte_identical']
out=dict(status='PASS_COMBINED_GEOMETRY_HEADLINE_NFG',headline='AspisR1.RPx_Deployed.deployed',combined_attempt=combined,combined_metrics={k:c[k] for k in ['command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']},combined_source_sha256=sha(E/'NFN_COMBINED_IMPORT.lean'),driver_source_sha256=sha(E/'NFN_Driver.lean'),driver_diff_sha256=sha(E/'NFN_DRIVER.diff'),driver_binary=obj(E/link/'NFN_Driver_BINARY_PIN.json'),walker_identity=obj(E/'NFN_WALKER_IDENTITY.json'),fixture_attempt=fixtures,fixtures=fx,results=rs,roots=len(rs),raw_graphs_equal_collectAxioms=True,standard_axioms_only=True,zero_unresolved_constants=True,incoherence_scan=dict(attempt=scan,modules=len(loaded),declarations=sum(x['declarations'] for x in loaded),references=sum(x['edges'] for x in loaded),dangling=0,duplicate_owners=0,import_mismatches=0,output_sha256=sha(E/'NFN_LOADED_scan.jsonl'),**{k:sr[k] for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps']}),scopes=scopes,release_cold_replay=False,security_target_established=False)
(E/'NFN_AUDIT.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(status=out['status'],roots=len(rs),scan=out['incoherence_scan'])))
