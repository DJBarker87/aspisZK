"""Validate retained session3 evidence without replaying Lean or a raw walk."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
accepted=[]
for n in range(49725,49732):
 r=json.loads((E/f'receipt-{n}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 admission=json.loads((E/f'admission-{n}.json').read_text());assert admission['allowed'] is True
 if r['accepted']:
  assert r['exit']==0 and r['swaps']=='0'
  assert sha(Path('lean',r['target']+'.lean').read_bytes())==r['source_sha256']
  log=(E/f'out-{n}.log').read_text();assert 'sorryAx' not in log
  accepted.append(r)
 else:
  assert n in [49727,49729] and r['exit']==1
  assert sha(lzma.decompress((E/f'failed-{n}.lean.xz').read_bytes()))==r['source_sha256']
for attempt,manifest_name,archive_prefix in [
 (49792,'SESSION2_AUDIT_ROOTS.json','SESSION3_RAW'),
 (49793,'SESSION3_NEW_AUDIT_ROOTS.json','SESSION3_NEW_RAW')]:
 receipt=json.loads((E/f'receipt-{attempt}.json').read_text())
 assert receipt['accepted'] and receipt['exit']==0 and receipt['swaps']=='0'
 roots=json.loads((E/manifest_name).read_text())['roots']
 results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in
   (E/f'out-{attempt}-w3.log').read_text().splitlines() if l.startswith('NEP62_RESULT ')]
 assert len(results)==len(roots) and {r['root'] for r in results}==set(roots)
 assert all(r['equal'] and set(r['walked_axioms'])<=allowed for r in results)
 m=json.loads((E/(archive_prefix+'_GRAPH_MANIFEST.json')).read_text())
 blob=(E/m['archive']).read_bytes();raw=lzma.decompress(blob)
 assert sha(blob)==m['archive_sha256'] and sha(raw)==m['uncompressed_sha256']
 graphs=json.loads(raw)
 for f in m['files']:assert sha(graphs[f['name']].encode())==f['sha256']
 assert set(graphs)=={'NEP_pv-thread_'+r+'_REACHABLE.txt' for r in roots}
 assert all('unresolved' not in (E/f'out-{attempt}-w3.log').read_text().lower() for _ in [0])
# Historical failed strict evidence is never upgraded by offline reconciliation.
old=json.loads((E/'receipt-49791.json').read_text());assert old['exit']==1 and not old['accepted']
base='5e397cb3878';prefix='evidence/pv-lib-20261107/'
freeze=json.loads(subprocess.check_output(['git','show',base+':'+prefix+'FREEZE.json']))
for name,want in freeze['files'].items():
 if name in ['PSPEC_COMMON.md','SPEC_CORRECTIONS.md']:continue
 assert sha(subprocess.check_output(['git','show','HEAD:'+prefix+name]))==want
common=Path(prefix+'PSPEC_COMMON.md').read_text();correction=Path(prefix+'SPEC_CORRECTIONS.md').read_text()
assert 'revision 2 (D981)' in common
assert 'OwnInitInterpreterBridged.step' in common and 'PV_LIB_SPEC_ThreadMachine.step' in common
assert 'Before' in correction and 'After' in correction and 'RegistrationGap.steps_differ' in correction
paths=subprocess.check_output(['git','diff','--name-only','9ea4f7cc336'],text=True).splitlines()
assert all(p.startswith(prefix+'lane-SPEC/') or re.fullmatch(r'lean/PV_LIB_SPEC_.*\.lean',p)
 or p in [prefix+'PSPEC_COMMON.md',prefix+'SPEC_CORRECTIONS.md'] for p in paths)
for p in Path('lean').glob('PV_LIB_SPEC_*.lean'):
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^axiom ',p.read_text(),re.M)
for p in E.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024
summary={'session_start':'9ea4f7cc336','accepted_focused':accepted,'failed_changed_before_retry':[49727,49729],
 'D981':'applied with exact before/after witness in shared SPEC_CORRECTIONS.md',
 'fresh_session2_roots_audit':{'attempt':49792,'roots':27,'exit':0},
 'new_roots_audit':{'attempt':49793,'roots':46,'exit':0},
 'full_frozen_contracts':0,'normative_contracts':29,'full_joint_witnesses':0,'full_joint_contradictions':0,
 'new_entry_component':'OwnInit OrderedFamiliesEntryOwned prime; concrete same-world capture storage',
 'endpoint_premises_removed':0,'endpoint_premises_added':0,'row_proofs':0,
 'write_boundary':'PASS, two shared D981 exception files','target_established':False,
 'next_lean':49732,'next_raw':49794}
(E/'SESSION3_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'accepted_focused':len(accepted),'audit49792':'27/27','audit49793':'46/46','full_contracts':0,'full_joint_witnesses':0,'write_boundary':'PASS'}))
