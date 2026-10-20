"""Read-only frozen-source/count audit; no SBF replay or leaf enumeration."""
from pathlib import Path
import hashlib, json, re, subprocess
root=Path.cwd(); base=root/'docs/research/100bit-spend-path-20261013'; ev=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p):
 return dict(path=str(p.relative_to(root)),sha256=sha(p),size_bytes=p.stat().st_size)
freeze=json.loads((base/'evidence/freeze-20261020/source-hashes.json').read_text())
frozen=[]
for name,digest in freeze['files'].items():
 if name.startswith(('crates/aspis-r1-cost-probe/src/','programs/r1-cost-probe/src/')):
  p=root/name
  assert sha(p)==digest, 'frozen verifier drift: '+name
  frozen.append(pin(p))
sites_path=base/'evidence/cu-bound4-20261020/sites.json'
sites=json.loads(sites_path.read_text())
entry=next(e for e in sites['source_level_sites'] if e['id']=='S-BINARY-PARENT-SHA')
a=[r for r in entry['rows'] if r['role']=='stage1']; b=[r for r in entry['rows'] if r['role']=='stage2']
assert len(a)==2 and len(b)==12
for r in a:
 assert (r['parent_hashes'],r['fixed_nonparent_sha_calls'],r['sha_calls'])==(447,148,595)
for r in b:
 assert r['fixed_nonparent_sha_calls']==3+3*12==39
 assert r['max_parent_hashes']==527
 assert r['sha_calls']==r['parent_hashes']+39<=566
 assert r['extra_parent_hashes']==527-r['parent_hashes']
 assert r['sha_calls']+r['extra_parent_hashes']==566
assert min(r['sha_calls'] for r in b)==545 and max(r['sha_calls'] for r in b)==563
compact=root/'crates/aspis-r1-cost-probe/src/compact.rs'
slots=list(map(int,re.search(r'pub const SLOT_NODES:.*?= \[(.*?)\];',compact.read_text())[1].split(',')))
assert slots==[146,146,128,172,172,150] and sum(slots)==914
assert sum(slots[3:])==494
# Compare the minimal retained privacy definitions verbatim modulo whitespace.
privacy=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
retained=base/'lean/QvStage2Privacy.lean'
def definition(text,name,kind='def'):
 start=re.search(r'^'+kind+r' '+re.escape(name)+r'\b',text,re.M).start()
 end=text.find('\n\n',start)
 return re.sub(r'\s+','',text[start:end if end!=-1 else None])
r=retained.read_text(); bindings=[]
for kind,name,file in [('abbrev','Fib','GamesR1PBin.lean'),('abbrev','NodeIdx','GamesR1PBin.lean'),('abbrev','RIdx','GamesR1PBin.lean'),('def','openedQ','LayoutR1P3Bin.lean'),('def','batchReadSet','EventsR1PBin.lean')]:
 # Abbreviations are single-line; source comments follow some immediately.
 source=(privacy/file).read_text()
 if kind=='abbrev':
  get=lambda s:re.sub(r'\s+','',re.search(r'^abbrev '+name+r'\b[^\n]*',s,re.M)[0])
 else:get=lambda s:definition(s,name,kind)
 assert get(source)==get(r), 'retained definition drift: '+name
 bindings.append(dict(name=name,source=str((privacy/file).relative_to(root)),line=source[:source.index(kind+' '+name)].count('\n')+1))
def header(s, name):
 start=s.index('theorem '+name+' ')
 return re.sub(r'\s+','',s[start:s.index(':=',start)])
assert header((privacy/'EventsR1PBin.lean').read_text(),'batch_length')==header(r,'batch_length')
funs=base/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'; text=funs.read_text()
def lean_def(name):
 start=text.index('def '+name+'\n')
 end=text.find('\n/--',start)
 return text[start:end]
resume=lean_def('verifier.resume'); finish=lean_def('verifier.finish_relation')
assert resume.count('.digest ')==3
assert 'Digest32' not in finish and '.digest ' not in finish
# callbacks and opaque arithmetic are explicitly outside this syntactic check.
probe=root/'crates/aspis-r1-cost-probe/src'
for name in ['weights.rs','fast_pairing.rs','fast_dots.rs']:
 src=(probe/name).read_text()
 assert not re.search(r'\b(?:sha256|Digest32)\b',src)
report=dict(schema='qv-stage2-count-crosscheck-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision=freeze['source_revision'],measurement_revision=sites['target_revision'],stage1_measured_rows=a,stage2_measured_rows=b,derivation=dict(slots=slots,batchB_supplied_cap=494,leaf_calls=36,parent_cap=527,resume=3,finish_relation_designated_digest_calls=0,stage2Budget='43*k+50',stage2_cap=566,stage1_cap=595,combined_verifier_core_cap=1161),retained_privacy_bindings=bindings,extracted_resume_direct_digest_occurrences=3,extracted_finish_relation_direct_digest_occurrences=0,frozen_verifier_pins=frozen,pins=[pin(p) for p in [sites_path,funs,retained,privacy/'GamesR1PBin.lean',privacy/'LayoutR1P3Bin.lean',privacy/'EventsR1PBin.lean',base/'design/WIRE-TX2-20261020.md',base/'design/QV-STAGE1-20261020.md',base/'evidence/proof-size-20261019/REPORT.md']],status='Conditional core allowance; existing syscall measurements agree. No source effect completeness or runtime replay claimed.')
(ev/'crosscheck.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'{len(frozen)} frozen verifier files match; retained privacy definitions match; 12 stage2 rows: 39 + parents <= 566; combined core <= 1161.')
