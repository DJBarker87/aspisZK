from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and sha(p)==f['sha256'] and p.stat().st_size==f['bytes'],p
assert {x['path'] for x in m['files']}=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
ts={t['module']:t for t in m['targets']};assert len(ts)==5;edges=0
for t in ts.values():
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 assert t['peak_aggregate_rss_bytes']<8*1024**3 and sha(r/t['source'])==t['source_sha256']
 d=r/'proof'/t['label'];p=json.loads((d/'preflight.json').read_text());rec=json.loads((d/'receipt.json').read_text())
 assert p['source_sha256']==t['source_sha256'] and rec['object_sha256']==t['object_sha256']
 assert p['limits']['lean_memory_mb']==4400 and p['limits']['threads']==1 and p['no_dependency_builds']
 assert sha(d/'profile.txt')==p['profile_sha256']
 for mod,pin in p['direct_imports'].items():
  if mod in ts:assert pin['sha256']==ts[mod]['object_sha256'];edges+=1
 log=(d/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 for ax in t['axioms'].values():assert set(ax)<={'propext','Classical.choice','Quot.sound'}
 assert t['compile_only']==(not bool(t['axioms']))
 ax={n:[a.strip() for a in aa.split(',')] for n,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
 ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",log)})
 assert ax==t['axioms']
for f in ['Types','Funs']:
 raw=(r/f'source-cut/generated/AspisR1S9CurrentCheckpointKDecoderV1/{f}.lean').read_text()
 normalized='\n'.join(line for line in raw.split('\n') if not re.match(r'set_option (maxHeartbeats|maxRecDepth) ',line))
 if f=='Funs':normalized=normalized.replace('import AspisR1S9CurrentCheckpointKDecoderV1.Types\n','import AspisR1S9CurrentCheckpointKDecoderV1.Types\nimport DecodeKOptionDiscriminantBridge\n')
 assert normalized==(r/f'sources/AspisR1S9CurrentCheckpointKDecoderV1/{f}.lean').read_text(),f
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.o','.a'}
print(f'PASS: 5 focused targets, {edges} coherent included imports; exact generated-source normalization, accepted source/reader same-value transport, canonicality. Full QM Result equality and caller/runtime/security OPEN.')
