import hashlib,json,pathlib
B=pathlib.Path(__file__).resolve().parent
H=json.load(open(B/'ELa_historical.json')); S=B.parent/'codex-cx-lowering2-20261026/src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for mode in ['default','devnet','pool']:
 d=B/('ELa_'+mode);r=json.load(open(d/'receipt.json'));assert r['exit_status']==0 and r['byte_identical']
 r['compiler_invocations']=[dict(path=str(p),sha256=sha(p),args=json.load(open(p))) for p in sorted((d/'diagnostics').glob('*.command.json'))]
 r['compiled_crates']=[p['args'][p['args'].index('--crate-name')+1] for p in r['compiler_invocations']]
 r['log_pins']={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in [d/'stdout.log',d/'time.log',d/'command.json',d/'receipt.json']}
 rows.append(r)
errors=[f['path'] for f in H['source_checks'] if sha(S/f['path'])!=f['expected_sha256']]
assert not errors
# Every repository compiler input from L186 matches this read-only cohort.
inputs={f['path']:f['sha256'] for b in H['builds'] for f in b['repository_compiler_inputs']}
assert all(sha(S/p)==h for p,h in inputs.items())
tables=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in sorted((B/'ELa_target').glob('**/out/circle_tables.rs'))]
assert tables and all(r['sha256']=='7fbe0464c940393bf8c59e676fd60d8411a296f0260f649fa27bbf9447a96491' for r in tables)
out=dict(status='all_three_frozen_ELF_pins_reproduced',builds=rows,postbuild_source_census=dict(checked=len(H['source_checks']),mismatches=errors),repository_compiler_inputs=dict(checked=len(inputs),mismatches=[]),generated_tables=tables,budget=dict(sbf=3,maximum=6,lean=0,kani=0),print_axioms='N/A: no new theorem',scope_count=1)
(B/'ELa_build_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['builds','generated_tables']}))
