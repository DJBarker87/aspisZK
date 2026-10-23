from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included'] and m['no_raw_llbc_or_binaries']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
assert {f['path'] for f in m['files']}=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
ids=json.loads((r/'source-identities.json').read_text())
for rel,h in ids['files'].items():assert sha(r/rel)==h
charon=json.loads((r/'extraction/charon/receipt.json').read_text());aeneas=json.loads((r/'extraction/aeneas/receipt.json').read_text())
for t in [charon,aeneas]:
 assert t['exit_status']==0 and not t['timed_out'] and t['swap_current_bytes']==0
 assert t['limits']=={'memory.high':'1073741824','memory.max':'2147483648','memory.swap.max':'0'}
 assert 'oom_kill 0' in t['memory_events_after'] and t['max_process_rss_kib']>0
assert charon['cgroup']==aeneas['cgroup'] and charon['llbc_sha256']==aeneas['llbc_sha256']
a=json.loads((r/'proof/admission-summary.json').read_text());assert all(a['checks'].values()) and a['scope_high_bytes']==1073741824 and a['scope_max_bytes']==2147483648 and a['swap_max_bytes']==0
assert charon['opaque_arithmetic_methods']==[] and charon['start_from']==['crate::secure_circle_producer']
assert set(aeneas['generated_lean'])=={'generated/AspisR1S9CurrentCircleProducerV1/Funs.lean','generated/AspisR1S9CurrentCircleProducerV1/Types.lean'}
for rel,h in aeneas['generated_lean'].items():assert sha(r/rel)==h
pins=json.loads((r/'NAMED-OWNER-SOURCE-PINS.json').read_text())['pins']
normalize=lambda s:re.sub(r'^set_option (maxHeartbeats|maxRecDepth) [^\n]+\n','',s,flags=re.M)
for part in ['Types','Funs']:
 raw=r/'generated/AspisR1S9CurrentCircleProducerV1'/f'{part}.lean';owned=r/'sources/AspisR1S9CurrentCircleProducerV1'/f'{part}.lean'
 assert sha(raw)==pins[part]['raw_sha256'] and sha(owned)==pins[part]['owner_source_sha256']
 if part=='Funs':assert normalize(raw.read_text())==owned.read_text()
 else:
  own=owned.read_text();start=own.index('-- Reversible naming-only discriminant expansion,');end=own.index('end AspisR1S9CurrentCircleProducerV1',start)
  stripped=own[:start]+own[end:];assert normalize(raw.read_text()).replace('@[discriminant isize]\n','')==stripped
 for forbidden in ['sorry','axiom ','native_decide','set_option maxHeartbeats','set_option maxRecDepth']:assert forbidden not in owned.read_text()
by={x['kind']:x for x in m['local_targets']}
for kind,t in by.items():
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 assert sha(r/t['source'])==t['source_sha256']
 p=json.loads((r/'proof'/kind/'preflight.json').read_text());assert p['source_sha256']==t['source_sha256'] and p['limits']['lean_memory_mb']==4400 and p['limits']['threads']==1
 assert sha(r/'proof'/kind/'profile.txt')==p['profile_sha256']
 assert 'error:' not in (r/'proof'/kind/'lean.log').read_text()
fpre=json.loads((r/'proof/funs/preflight.json').read_text());apre=json.loads((r/'proof/audit/preflight.json').read_text())
assert fpre['direct_imports']['AspisR1S9CurrentCircleProducerV1.Types']['sha256']==by['types']['object_sha256']
assert apre['direct_imports']['AspisR1S9CurrentCircleProducerV1.Funs']['sha256']==by['funs']['object_sha256']
owner=json.loads((r/'proof/complete-owner-pins.json').read_text());assert owner=={k+'.olean':by[k.lower()]['object_sha256'] for k in ['Types','Funs']}
log=(r/'proof/audit/lean.log').read_text();ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);assert len(ax)==7 and 'sorryAx' not in log
assert {n:[a.strip() for a in aa.split(',')] for n,aa in ax}==m['axioms']
for _,aa in ax:assert {a.strip() for a in aa.split(',')}<={'propext','Classical.choice','Quot.sound'}
old=json.loads((r/'history/modern-arrow-rejected/aeneas/receipt.json').read_text());assert old['exit_status']==2
modern=json.loads((r/'history/modern-arrow-rejected/charon/receipt.json').read_text());assert modern['source_identity_sha256']==charon['source_identity_sha256']
assert 'Arrow types are not supported yet' in (r/'history/modern-arrow-rejected/aeneas/stdout.log').read_text()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.o','.a'}
print('PASS: exact current Rust source; reused old tools resolve callback extraction; coherent focused owners; seven standard definition axiom reports. Mapper correctness/caller/security OPEN.')
