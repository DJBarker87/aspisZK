#!/usr/bin/env python3
"""Freeze/check the measured task-owned source closure and executable inputs."""
import hashlib,json,pathlib,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[2]
assert str(ROOT)=='/home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909' and not (ROOT/'.git').exists()
OLD=ROOT/'docs/research/v8-no-work-100-20260907/experiments'
OUT=HERE/'evidence/build-inputs.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def files():
    chosen={ROOT/'Cargo.toml',ROOT/'Cargo.lock'}
    for folder in [ROOT/'crates',ROOT/'programs',OLD,ROOT/'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness',HERE/'inbox']:
        for p in folder.rglob('*'):
            if 'target' not in p.parts and p.is_file() and p.suffix in {'.rs','.toml','.lock'}:
                chosen.add(p)
    chosen.add(HERE/'driver.rs')
    return {str(p.relative_to(ROOT)):sha(p) for p in sorted(chosen)}
def artifacts():
    chosen=[p for p in (ROOT/'artifacts').glob('*') if p.is_file()]
    chosen += [ROOT/'artifacts/inbox/aspis_v8_atomic_inbox.so',OLD/'performance-svm/target/release/aspis-v7-pair-forest-combined-rejection',OLD/'performance-host/target/release/aspis-v8-performance-host']
    chosen += list((ROOT/'fixtures').glob('*.bin')) + list((ROOT/'proving/proofs').glob('*.bin'))
    return {str(p.relative_to(ROOT)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(chosen)}
current={'base':'4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e','source_files':files(),'executable_and_fixture_inputs':artifacts()}
if sys.argv[1:] == ['capture']:
    assert not OUT.exists(), 'Do not overwrite a measured source lock'
    OUT.write_text(json.dumps(current,indent=2)+'\n')
else:
    assert sys.argv[1:] == ['check']
    expected=json.loads(OUT.read_text())
    assert current==expected, 'Source/artifact drift; investigate before running or rebuilding'
print(json.dumps({'source_files':len(current['source_files']),'artifacts':len(current['executable_and_fixture_inputs']),'status':'matched' if sys.argv[1]=='check' else 'captured'}))
