from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent;base=r.parent.parent;m=json.loads((r/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
for t in m['targets']+[m['reused_shared_target']]:
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 l=(r/('shared-table/proof/lean.log' if t['name']=='S9FactorTableSemanticsV1' else 'proof/'+t['name']+'/lean.log')).read_text();assert 'sorryAx' not in l and 'error:' not in l
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',l):assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
d=json.loads((r/'source-dependencies.json').read_text())
for x in d['exact_sources']:assert hashlib.sha256((base/x['path']).read_bytes()).hexdigest()==x['sha256']
assert hashlib.sha256((r/d['shared_table_accepted_source']).read_bytes()).hexdigest()==d['shared_table_source_sha256']
rr=json.loads((r/'source-control-reuse.json').read_text());original=(base/rr['source']).read_text();proof=(r/'sources/S9StatementSourceLoopFactsV1.lean').read_text()
spans=[original[original.index('private def statementTail'):original.index('private def rangeMeasure')],original[original.index('private theorem outer_cont_has_execution'):original.index('private def statementOuterStep')]]
for raw,pins in zip(spans,rr['spans']):
 changed=raw.replace('private def statementTail','def statementTail').replace('private theorem statementTail_success_cont','theorem statementTail_success_cont').replace('private theorem inner_cont_has_next','theorem inner_cont_has_next').replace('private theorem inner_done_same_factors','theorem inner_done_same_factors').replace('private theorem outer_cont_has_execution','theorem outer_cont_has_execution').replace('private theorem outer_done_same_factors','theorem outer_done_same_factors')
 assert hashlib.sha256(raw.encode()).hexdigest()==pins['input_sha256'] and hashlib.sha256(changed.encode()).hexdigest()==pins['included_sha256'] and changed in proof
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.dll'}
print('PASS: actual statement factor source phase has retained D18 meanings; source-only/standard axioms/bounded scope')
