from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
assert {x['path'] for x in m['files']}=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
ts={t['module']:t for t in m['targets']};assert len(ts)==4;edges=0
for t in ts.values():
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 assert t['peak_aggregate_rss_bytes']<8*1024**3 and sha(r/t['source'])==t['source_sha256']
 d=r/'proof'/t['label'];pre=json.loads((d/'preflight.json').read_text());rec=json.loads((d/'receipt.json').read_text())
 assert pre['source_sha256']==t['source_sha256'] and rec['object_sha256']==t['object_sha256']
 assert pre['limits']['lean_memory_mb']==4400 and pre['limits']['threads']==1 and pre['no_dependency_builds']
 assert pre['profile_sha256']==sha(d/'profile.txt')
 for mod,pin in pre['direct_imports'].items():
  if mod in ts:assert pin['sha256']==ts[mod]['object_sha256'];edges+=1
 log=(d/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 ax={n:[a.strip() for a in aa.split(',')] for n,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)};ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",log)})
 assert ax==t['axioms'] and ax
 for aa in ax.values():assert set(aa)<={'propext','Classical.choice','Quot.sound'}
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.o','.a','.pyc'}
assert sha(r/'source-origin/ProductionPairCutV1-Funs.lean.txt')==m['qualified_source_sha256']
k=(r/'sources/S9ActualProcessKindTensorReachedV1.lean').read_text()
assert 'hs2 : self.variant=transport.Variant.S2' in k and 'hnotD' in k
for n in [1,2,3,5,6]:assert f'theorem row_kind{n}' in k
trace=(r/'sources/S9ActualRegularKindsTraceV1.lean').read_text()
assert 'KindCall self 2#usize' in trace and 'KindCall self 1#usize' in trace
pair=(r/'sources/S9ActualPairTensorCallsV1.lean').read_text()
assert 'def TensorRegularTrace' in pair and 'theorem actual_pair_success_tensor_calls' in pair
assert 'process_kind_success_reaches_tensor' in pair
assert 'tensor' not in (r/'sources/S9ActualPairRegularPrefixV1.lean').read_text().split('theorem actual_pair_success_regular_prefix',1)[1].split(':= by',1)[0]
assert 'error:' in (r/'history/kind-v2/lean.log').read_text()
assert 'error:' in (r/'history/trace-v1/lean.log').read_text()
assert 'error:' in (r/'history/prefix-v1/lean.log').read_text()
print(f'PASS:4 focused targets,{edges} coherent included imports; SAME accepted Pair actual3/5-kind tensor traces/scratch/powers/f/n, standard axioms. Full Pair math/Rust/runtime/S9/security OPEN.')
