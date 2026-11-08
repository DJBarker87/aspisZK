"""Offline evidence validation; does not run Lean or repeat raw walks."""
import pathlib,json,lzma,hashlib,subprocess,re
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE');sha=lambda b:hashlib.sha256(b).hexdigest()
compiled=[]
for a in [49920,49921,49922]:
 r=json.loads((E/f'receipt-{a}.json').read_text())
 assert r['accepted']==(a!=49920)
 assert json.loads((E/f'turn-{a}.json').read_text())['exit']==0
 assert json.loads((E/f'admission-{a}.json').read_text())['allowed'] is True
 for p,v in [('MemoryHigh','6G'),('MemoryMax','8G'),('MemorySwapMax',0),('TasksMax',64),('Lean_M',7000)]:assert r['caps'][p]==v
 if a==49920:
  assert sha(lzma.decompress((E/f'failed-input-{a}.lean.xz').read_bytes()))==r['source_sha256']
 else:
  p=pathlib.Path('lean',r['target']+'.lean');assert sha(p.read_bytes())==r['source_sha256']
  assert r['exit']==0 and r['swaps']=='0'
  assert r['axioms_summary_based'] and all('sorryAx' not in l for l in r['axioms_summary_based'])
  compiled.append({k:r[k] for k in ['attempt','target','source_revision','source_sha256','exit','wall','peak_rss_kbytes','swaps']})
raw=json.loads((E/'SESSION3_RAW_AUDIT.json').read_text());roots=json.loads((E/'SESSION3_AUDIT_ROOTS.json').read_text())['roots']
assert raw['attempt']==49692 and raw['receipt']['accepted'] and raw['root_count']==len(roots)==33
assert raw['unresolved']==raw['summary_mismatches']==0
assert {r['root'] for r in raw['roots']}==set(roots)
for r in raw['roots']:
 assert r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
assert raw['receipt']['swaps']=='0'
assert json.loads((E/'turn-49692.json').read_text())['exit']==0
assert json.loads((E/'admission-49692.json').read_text())['allowed'] is True
man=json.loads((E/'SESSION3_RAW_GRAPH_MANIFEST.json').read_text());archive=(E/'SESSION3_RAW_GRAPH_ARCHIVE.json.xz').read_bytes();plain=lzma.decompress(archive)
assert sha(archive)==man['archive_sha256'] and sha(plain)==man['uncompressed_sha256']
files=json.loads(plain)
for r in man['files']:assert sha(files[r['name']].encode())==r['sha256']
for r in roots:assert any(n.startswith('NEP_pv-thread_'+r+'_') and n.endswith('_REACHABLE.txt') for n in files)
# Only module/root and explicit reached-constructor arrays differ in the driver.
old=pathlib.Path('lean/PV_LIB_SLICE_RawAudit2.lean').read_text();new=pathlib.Path('lean/PV_LIB_SLICE_RawAudit3.lean').read_text()
def normalized(s):
 s=re.sub(r'  let \(modules, roots\) :=[\s\S]*?\n  let env', '  ROOTS\n  let env',s)
 return re.sub(r'for aux in #\[[^\n]*\] do','for aux in CONSTRUCTORS do',s)
assert normalized(old)==normalized(new)
# Verify exact retained read-only input bytes, including compressed snapshots.
snapshots=[]
for p in (E/'session3-inputs').iterdir():
 n=p.name.removesuffix('.xz');rawbytes=lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes()
 if n=='spec-ToVec-component.lean.txt':rev='a84dc05c68e';path='lean/PV_LIB_SPEC_ToVec.lean'
 elif n.startswith('spec-'):rev='a84dc05c68e';path='evidence/pv-lib-20261107/'+n[5:]
 elif n.startswith('base-'):rev='5e397cb3878';path='evidence/pv-lib-20261107/'+n[5:]
 elif n.startswith('template-'):
  rev='research';leaf=n[9:];path=('evidence/lib-map-20261107/' if leaf.startswith('LIB0_') else 'evidence/rowspec-lead-20261107/')+leaf
 else:raise AssertionError(n)
 assert rawbytes==subprocess.check_output(['git','show',rev+':'+path])
 snapshots.append(dict(snapshot=str(p),revision=rev,path=path,sha256=sha(rawbytes)))
changed=subprocess.check_output(['git','diff','--name-only','e440502a81e'],text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
allowed={'lean/PV_LIB_SLICE_Spec_f21.lean','lean/PV_LIB_SLICE_RawAudit3.lean'}
assert all(p in allowed or p.startswith(str(E)+'/') for p in changed)
for f in allowed:
 s=pathlib.Path(f).read_text();assert not re.search(r'^\s*(axiom|sorry|admit)\b',s,re.M)
index=json.loads((E/'SESSION3_CONTRACT_INDEX.json').read_text());assert index['full_contracts']==index['full_source7_joint_witnesses']==index['full_source7_joint_contradictions']==0
out=dict(validation='PASS',source_head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),focused_passes=compiled,failed_changed_before_retry=[49920],strict_raw=dict(attempt=49692,roots=33,exit=0,wall=raw['receipt']['wall'],peak_rss_kbytes=raw['receipt']['peak_rss_kbytes'],swaps='0',unresolved=0,mismatches=0),snapshots=snapshots,write_boundary='PASS',cohort='isolated pinned STX; no coherent D937/STX combination claimed',full_contracts=0,source7_joint_witnesses=0,source7_joint_contradictions=0,remaining='SESSION3_f21_COMPARISON.md full-contract gate; finish f21 before next row',next_lean=49923,next_raw=49693)
(E/'SESSION3_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: 2 focused compiles; 33 strict raw roots; write boundary; full targets still0/11 and0/1.')
