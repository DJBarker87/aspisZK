"""Summarize raw ax2 output; no standard-axiom or coherence waiver."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rows(a):
 r=obj(E/a/'receipt.json');assert r['exit_status']==0
 return [json.loads(l[len('NEP_RESULT '):]) for l in (E/a/'stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
fixtures=rows('NFP_L049');assert {r['root']:r['walked_axioms'] for r in fixtures}==expected
assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] for r in fixtures)
manifest=obj(E/'NFP_AUDIT_ROOTS.json');results=[]
for i,g in enumerate(manifest['groups']):
 a=f'NFP_L{53+i:03}';found=rows(a);assert [r['root'] for r in found]==g
 for r in found:
  assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
  n='NEP_proof'+str(i)+'_'+r['root']+'_REACHABLE.txt';archive=E/(n+'.xz');raw=lzma.decompress(archive.read_bytes());h=hashlib.sha256(raw).hexdigest();assert (E/(n+'.sha256')).read_text().split()[0]==h
  results.append({**r,'attempt':a,'graph_archive':archive.name,'uncompressed_sha256':h,'compressed_sha256':sha(archive)})
assert len(results)==len(manifest['roots']) and len({r['root'] for r in results})==len(results)
extra=rows('NFP_L060')
assert {r['root'] for r in extra}=={'AspisR1.NFM_Single.domains','AspisR1.NFG_PushRoot.private_domains'}
for r in extra:
 assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
 n='NEP_extra_'+r['root']+'_REACHABLE.txt';archive=E/(n+'.xz');raw=lzma.decompress(archive.read_bytes());h=hashlib.sha256(raw).hexdigest();assert (E/(n+'.sha256')).read_text().split()[0]==h
 results.append({**r,'attempt':'NFP_L060','graph_archive':archive.name,'uncompressed_sha256':h,'compressed_sha256':sha(archive)})
scan=[json.loads(l) for l in (E/'NFP_LOADED_scan.jsonl').read_text().splitlines()];assert all(r['imports_match'] and not r['dangling'] for r in scan)
s=(E/'NFP_Driver.lean').read_text();canonical=(E.parent/'axaudit2-20261102/NEP_Driver.lean').read_text();assert s[s.index('  let env ← importModules'):]==canonical[canonical.index('  let env ← importModules'):]
walker=obj(E/'NFP_WALKER_PIN.json');assert walker['unchanged']
core=(E/'NFP_Scanner.lean').read_text();a=core.index('namespace NER\n');b=core.index('end NER\n',a)+len('end NER\n');assert hashlib.sha256(core[a:b].encode()).hexdigest()==walker['scanner_core_sha256']
# Pin the same optimized executable across every invocation.
driver=obj(E/'NFP_L048/NFP_Driver_BINARY_PIN.json');scanner=obj(E/'NFP_L051/NFP_Scanner_BINARY_PIN.json')
for i in [49]+list(range(53,61)):assert obj(E/f'NFP_L{i:03}/NFP_Driver_BINARY_PIN.json')==driver
assert obj(E/'NFP_L052/NFP_Scanner_BINARY_PIN.json')==scanner
attempts=[json.loads(l) for l in (E/'NFP_ATTEMPTS.jsonl').read_text().splitlines()]
formal=[r for r in attempts if r['kind']!='kani'];assert len(formal)==60 and len({r['attempt'] for r in formal})==60
for module in manifest['modules']:
 p=E/(module+'.lean');rs=[r for r in formal if r['kind']=='lean' and r['module']==module and r['exit_status']==0]
 assert rs and rs[-1]['source_hashes']['NFP_generated/'+module+'.lean']==sha(p)
 assert all('sorryAx' not in line for line in rs[-1]['print_axioms'])
audit=dict(status='PASS_COHERENT_SUPPORT_NOT_QUERY_ROW_CLOSURE',headline='AspisR1.RPx_Deployed.deployed',combined_attempt='NFP_L046',roots=len(results),new_top_theorems=len(manifest['roots'])-7,results=results,fixtures=fixtures,fixture_attempt='NFP_L049',walker_unchanged=True,audit_action_unchanged=True,walker_sha256=walker['sha256'],driver_source_sha256=sha(E/'NFP_Driver.lean'),driver_binary=driver,scanner_binary=scanner,scanner_core_unchanged=True,incoherence_scan=dict(attempt='NFP_L052',modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=0,import_mismatches=0,output_sha256=sha(E/'NFP_LOADED_scan.jsonl')),raw_graphs_equal_collectAxioms=True,standard_axioms_only=True,zero_unresolved_constants=True,legacy_accumulation_packet_excluded=True,query_rows_closed=0,cold_release_replay=False,formal_scopes=[{k:r[k] for k in ['attempt','module','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']} for r in formal])
(E/'NFP_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps({k:audit[k] for k in ['status','roots','new_top_theorems','incoherence_scan']}))
