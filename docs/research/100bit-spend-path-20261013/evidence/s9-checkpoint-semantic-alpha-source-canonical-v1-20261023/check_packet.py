from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
assert {f['path'] for f in m['files']}=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
targets={x['module']:x for x in m['targets']};assert len(targets)==5;edges=0
for t in targets.values():
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 assert t['peak_aggregate_rss_bytes']<8*1024**3 and sha(r/t['source'])==t['source_sha256']
 d=r/'proof'/t['label'];p=json.loads((d/'preflight.json').read_text());rec=json.loads((d/'receipt.json').read_text())
 assert p['source_sha256']==t['source_sha256'] and rec['object_sha256']==t['object_sha256']
 assert p['limits']['lean_memory_mb']==4400 and p['limits']['threads']==1 and p['no_dependency_builds']
 assert sha(d/'profile.txt')==p['profile_sha256']
 for mod,pin in p['direct_imports'].items():
  if mod in targets:assert pin['sha256']==targets[mod]['object_sha256'];edges+=1
 log=(d/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);empty=re.findall(r"'([^']+)' does not depend on any axioms",log)
 assert ax or empty
 assert ({n:[a.strip() for a in aa.split(',')] for n,aa in ax}|{n:[] for n in empty})==t['axioms']
 for _,aa in ax:assert {a.strip() for a in aa.split(',')}<={'propext','Classical.choice','Quot.sound'}
model=(r/'sources/S9CheckpointSemanticReadOnlyV1.lean').read_text();reuse=json.loads((r/'THIN-REUSE-PINS.json').read_text());assert sha(r/'sources/S9CheckpointSemanticReadOnlyV1.lean')==reuse['model_source_sha256']
assert len(reuse['declarations'])==6
for pin in reuse['declarations']:
 raw=(r/pin['retained_span']).read_text();assert hashlib.sha256(raw.encode()).hexdigest()==pin['exact_span_sha256'];new=raw
 for old,rep in pin['replacements']:new=new.replace(old,rep)
 assert hashlib.sha256(new.encode()).hexdigest()==pin['emitted_span_sha256'] and new in model
assert [x for x in model.splitlines() if x.startswith('import ')]==['import Stage2ContinuationTypes']
pins=json.loads((r/'GENERATED-HELPER-PINS.json').read_text());raw=(r/'source-origin/generated-helper.lean.txt').read_text();assert hashlib.sha256(raw.encode()).hexdigest()==pins['selected_body_sha256']
expected=raw.replace('def verifier.read_checkpoint_semantic_alpha\n','def source (read : ReadK)\n').replace('verifier.Reader.k','read');assert raw.count('verifier.Reader.k')==10 and expected in (r/'sources/S9CheckpointSemanticAlphaSourceV1.lean').read_text()
for d in (r/'history').iterdir():assert 'error' in (d/'lean.log').read_text().lower()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.o','.a'}
print(f'PASS:5 focused targets,{edges} coherent included import edges, exact thin/source reuse, strict same-resume alpha canonicality, standard axioms. Native source adoption/S9/security OPEN.')
