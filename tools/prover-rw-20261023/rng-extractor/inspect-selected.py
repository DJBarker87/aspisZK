"""Inspect actual selected LLBC and compiler pins without translation/build."""
from pathlib import Path
import hashlib,json,subprocess
R=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src')
D=R/'tools/prover-rw-20261023/rng-extractor'
O=R.parent/'rng-extractor'
p=D/'ProverRwRngExtractorselected64.llbc'
data=json.loads(p.read_text())['translated']
selected=[]
for f in data['fun_decls']:
    if f is None:continue
    name=json.dumps(f['item_meta']['name'])
    if any(t in name for t in ['prove_for_proof_accounts','generate_for_mask_nonce','map_err','"from"','"fill"']):
        selected.append(f)
files=[]
for f in data['files']:
    name=f['name'].get('Local')
    if not name or f.get('contents') is None:continue
    source=Path(name)
    if not source.is_absolute():source=R/source
    if not source.is_file():continue
    content=f['contents'].encode()
    files.append(dict(path=name,llbc_sha256=hashlib.sha256(content).hexdigest(),
        current_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        equal=content==source.read_bytes()))
rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+nightly-2026-06-01','-Vv'],text=True)
assert '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in rustc
locks={}
for q in [R/'Cargo.lock',D/'synthetic/Cargo.lock']:
    text=q.read_text()
    assert 'name = "getrandom"\nversion = "0.3.4"' in text
    if q==R/'Cargo.lock':assert 'name = "zeroize"\nversion = "1.8.1"' in text
    locks[str(q)]=dict(sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
out=dict(schema='ProverRwRngExtractor-selected-source-assessment-v1',
    llbc=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size),
    selected_declarations=selected,source_bindings=files,rustc=rustc,locks=locks,
    target_information=data['target_information'],options=data['options'],
    assessment='Actual unmodified RealR1_client proof-account caller, mutable FnMut policy, selected 64-byte generator, actual inner map_err closure and From are present with structured bodies. getrandom::fill is an opaque OS primitive, not an extraction failure. Its full signature has no explicit provider/read-history argument. No actual-caller Aeneas translation, event/status refinement, native primitive association or OS law was established. Effect/state transport remains required, not silently postulated.',
    print_axioms='N/A: read-only declaration inventory; no Lean invocation')
(O/'selected-source-assessment.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(function_ids=[f['def_id'] for f in selected],source_bindings=len(files),all_sources_match=all(f['equal'] for f in files),llbc=out['llbc'])))
