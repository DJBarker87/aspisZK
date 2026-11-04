from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul8-20261104'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
obj=lambda p:json.loads(Path(p).read_text())
def results(attempt):
 r=obj(E/attempt/'receipt.json');assert r['exit_status']==0
 return [json.loads(line[len('NEP_RESULT '):]) for line in (E/attempt/'stdout.log').read_text().splitlines() if line.startswith('NEP_RESULT ')]
fixture=results('NFM_L024');expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
assert {r['root']:r['walked_axioms'] for r in fixture}==expected
assert all(r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms']) for r in fixture)
manifest=obj(E/'NFM_AUDIT_ROOTS.json');out=[]
for index,group in enumerate(manifest['groups']):
 a=f'NFM_L{28+index:03}';rows=results(a);assert [r['root'] for r in rows]==group
 for r in rows:
  assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
  base='NEP_proof'+str(index)+'_'+r['root']+'_REACHABLE.txt';p=E/(base+'.xz');raw=lzma.decompress(p.read_bytes());h=hashlib.sha256(raw).hexdigest()
  assert (E/(base+'.sha256')).read_text().split()[0]==h
  out.append({**r,'attempt':a,'graph_archive':p.name,'uncompressed_sha256':h,'compressed_sha256':sha(p)})
assert len(out)==len(manifest['roots'])==124 and len({r['root'] for r in out})==124
scan=[json.loads(l) for l in (E/'NFM_LOADED_scan.jsonl').read_text().splitlines()]
assert all(r['imports_match'] and not r['dangling'] for r in scan)
source=(E/'NFM_Driver.lean').read_text();canonical=(E.parent/'axaudit2-20261102/NEP_Driver.lean').read_text()
assert source[source.index('  let env ← importModules'):]==canonical[canonical.index('  let env ← importModules'):], 'ax2 audit action changed'
original_scanner=(P/'NFI_Driver.lean').read_text();a=original_scanner.index('namespace NER\n');b=original_scanner.index('end NER\n',a)+len('end NER\n');core=original_scanner[a:b]
newscanner=(E/'NFM_Scanner.lean').read_text();assert core in newscanner and hashlib.sha256(core.encode()).hexdigest()==obj(E/'NFM_SCANNER_CORE.json')['sha256']
walker=obj(E/'NFM_WALKER_PIN.json');assert walker['walker_unchanged']
# Each executed binary has the same hash as its optimized link result.
driver=obj(E/'NFM_L023/NFM_Driver_BINARY_PIN.json');scanner=obj(E/'NFM_L026/NFM_Scanner_BINARY_PIN.json')
for i in [24]+list(range(28,61)):assert obj(E/f'NFM_L{i:03}/NFM_Driver_BINARY_PIN.json')==driver
assert obj(E/'NFM_L027/NFM_Scanner_BINARY_PIN.json')==scanner
attempts=[json.loads(l) for l in (E/'NFM_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(attempts)==160 and len({r['attempt'] for r in attempts})==160
assert sum(r['kind']=='kani' for r in attempts)==100
successful={r['module']:r for r in attempts if r['kind']=='lean' and r['exit_status']==0}
for m,r in successful.items():
 assert r['source_hashes']['NFM_generated/'+m+'.lean']==sha(E/(m+'.lean'))
 assert all('sorryAx' not in s for s in r['print_axioms'])
scopes=[{k:r[k] for k in ['attempt','module','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']} for r in attempts if r['kind']!='kani']
audit=dict(status='PASS_COMBINED_HEADLINE_NFM',headline='AspisR1.RPx_Deployed.deployed',combined_attempt='NFM_L021',roots=len(out),new_roots=len(manifest['new_roots']),results=out,fixtures=fixture,fixture_attempt='NFM_L024',walker_unchanged=True,walker_sha256=walker['sha256'],audit_action_unchanged=True,driver_source_sha256=sha(E/'NFM_Driver.lean'),driver_binary=driver,scanner_binary=scanner,scanner_core_unchanged=True,scanner_core_sha256=obj(E/'NFM_SCANNER_CORE.json')['sha256'],incoherence_scan=dict(attempt='NFM_L027',modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=0,import_mismatches=0,output_sha256=sha(E/'NFM_LOADED_scan.jsonl')),raw_graphs_equal_collectAxioms=True,standard_axioms_only=True,zero_unresolved_constants=True,budget=dict(kani=100,lean_audit=60,extraction=0),scopes=scopes,sibling_geometry_imported=False,cached_development_cohort=True,cold_release_replay=False)
(E/'NFM_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps({k:audit[k] for k in ['status','roots','new_roots','incoherence_scan','budget']}))
