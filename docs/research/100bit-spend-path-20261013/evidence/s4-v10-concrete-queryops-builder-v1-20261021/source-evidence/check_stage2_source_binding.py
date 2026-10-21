from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parent; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(r/'candidate-current.rs')=='5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794'
assert sha(r/'Stage2ContinuationQueryAdvance.lean')=='9d7eb55883d5f8215d0eddaea737b60ace37c16a4a498d1f2f903110f14fbbfd'
assert sha(r/'Stage2ContinuationQueryLoop.lean')=='c398ba41273939ac739a064eee492976988027ff1b1d6f33657480b17aed0def'
f=json.loads((r/'final-binding.json').read_text())
assert f['raw_generated']['generated/AspisR1Stage2/Funs.lean']==sha(r/'generated-Funs.lean')
assert f['bindings']['query-advance-binding']['whole_accumulator_and_query_bodies']
assert f['bindings']['query-loop-binding']['entire_three_definitions']
assert f['bindings']['query-loop-binding']['only_callee_parameterized']=='verifier.candidate.query_values'
assert f['bindings']['query-loop-binding']['generated_bodies_sha256']==json.loads((r/'query-loop-binding.json').read_text())['generated_bodies_sha256']
assert f['bindings']['query-advance-binding']['parameterized_bodies_sha256']==json.loads((r/'query-advance-binding.json').read_text())['parameterized_bodies_sha256']
# Pin the current Rust source to the exact retained Charon/Aeneas run.
chain=json.loads((r/'current-stage2-source-binding.json').read_text())['rust_to_emission_chain']
assert chain['attempt']=='checkpoint-k-inline-55'
assert chain['candidate_source_sha256']==sha(r/'candidate-current.rs')
assert chain['generated_funs_sha256']==sha(r/'generated-Funs.lean')
ex=r/chain['source_manifest'].rsplit('/',1)[0]
source=json.loads((ex/'source.json').read_text())
charon=json.loads((ex/'charon-input.json').read_text())
llbc=json.loads((ex/'llbc.json').read_text())
cr=json.loads((ex/'charon-receipt.json').read_text())
aeneas=json.loads((ex/'aeneas-receipt.json').read_text())
pins=json.loads((ex/'final-extraction-pins.json').read_text())
candidate_path='crates/aspis-r1-cost-probe/src/candidate.rs'
assert source['source_hashes'][candidate_path]==sha(r/'candidate-current.rs')
assert charon['source_hashes'][candidate_path]==sha(r/'candidate-current.rs')
assert charon['source_revision']==chain['source_revision']
assert cr['exit_status']==0 and llbc['has_errors'] is False
assert llbc['sha256']==chain['llbc_sha256']
assert cr['command'][cr['command'].index('--dest-file')+1]==llbc['path']
assert aeneas['exit_status']==0 and aeneas['command'][-1]==llbc['path']
assert pins['attempt']==chain['attempt']
assert pins['source_revision']==chain['final_source_revision']
assert pins['extraction_input_declared_revision']==chain['source_revision']
assert pins['extraction_source_hashes_match_final_revision'] is True
assert pins['llbc']['sha256']==llbc['sha256']
assert next(x for x in pins['generated_files'] if x['path'].endswith('/Funs.lean'))['sha256']==sha(r/'generated-Funs.lean')
# Verify the exact generator transforms still reconstruct the checked source modules from the pinned emitted bodies.
E=Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/evidence/stage2-continuation-20261020/harness')
subprocess.run(['python3',str(E/'prepare-query-advance.py'),'--check'],check=True)
subprocess.run(['python3',str(E/'prepare-loop-fact.py'),'--check'],check=True)
subprocess.run(['python3',str(r/'check_query_callsite.py')],check=True)
print('PASS current Rust source, emitted bodies, parameterized query/loop adapters, and source-operation order are pinned')
