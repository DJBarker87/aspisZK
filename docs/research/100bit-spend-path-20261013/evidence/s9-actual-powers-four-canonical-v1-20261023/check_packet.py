from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());base=r.parent.parent
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'];assert p.stat().st_size==f['bytes']
for t in m['targets']:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 d=r/'proof'/t['name'];p=r/t['source'];assert hashlib.sha256(p.read_bytes()).hexdigest()==t['source_sha256']
 log=(d/'lean.log').read_text();assert 'sorryAx' not in log and 'native_decide' not in log and 'error:' not in log
 for block in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(x.strip() for x in block.split(','))<={'propext','Classical.choice','Quot.sound'}
 assert not json.loads((d/'closure-summary.json').read_text())['missing']
 assert not re.search(r'\bsorry\b|\bnative_decide\b|(?m:^axiom\s)',p.read_text())
for d in json.loads((r/'source-dependencies.json').read_text())['exact_sources']:
 p=base/d['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==d['sha256']
funs=(base/m['current_source']['path']).read_text();a=funs.index('def _root_.AspisR1S9ProductionPairCutV1.weights.powers_loop.body');b=funs.index('/-- [aspis_r1_cost_probe::weights::kpowers]',a)
assert funs[a:b]==(r/'current-source/powers-span.lean.txt').read_text()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
assert all(a['identical'] for a in json.loads((r/'portability/cohort-identity.json').read_text())['exact_byte_identity_anchors'])
print('PASS: four focused actual powers producer proofs; source-only, standard axioms, bounded scope')
