#!/usr/bin/env python3
"""Only the new bounded recorded-C1 access implementation; no old suite/replay."""
import hashlib, importlib.util, json, os, subprocess, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OLD = REPO / 'docs/research/v8-no-work-100-20260907/experiments'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    # Keep the authenticate slice literal; imports alone are scoped for the
    # small standalone harness. No fallback or alternate authentication code.
    start, stop = 'pub const OPEN_FIBRES', 'pub struct Decoder'
    original = (OLD/'authenticated_c1.rs').read_text().split(start, 1)[1].split(stop, 1)[0]
    copied = (HERE/'ExtractionAuthenticatedC1.rs').read_text().split(start, 1)[1]
    assert original == copied
    spec = importlib.util.spec_from_file_location('completion_checks', HERE/'check.py')
    checks = importlib.util.module_from_spec(spec); spec.loader.exec_module(checks)
    evidence = Path(tempfile.mkdtemp(prefix='ExtractionEvidence-', dir=HERE))
    inputs = [HERE/n for n in ['ExtractionRecordedC1.rs', 'ExtractionAuthenticatedC1.rs',
        'ExtractionRecordedC1Control.rs', 'ExtractionCheck.py', 'check.py']]
    inputs += [REPO/'crates/aspis-core/src'/n for n in ['field.rs', 'state_only_private_merkle.rs', 'v7_merkle208.rs']]
    inputs += [OLD/'authenticated_c1.rs', OLD/'recovered_witness.rs']
    report = {'source_revision': subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
        'sources': {str(p.relative_to(REPO)): sha(p) for p in inputs},
        'scope': 'New finite recorded-prefix to existing authenticated first256-fibre input. No decoder precompute or payment execution.',
        'historical_Lean_cache': 'NOT IMPORTED', 'checks': []}
    with tempfile.TemporaryDirectory(prefix='aspis-extraction-access-') as temp:
        binary = Path(temp)/'extraction-access'
        # Optimized; time is expected in one small Rust compilation and tiny
        # fixed 521-record controls, not dense elimination or full tree creation.
        command = ['rustc','--edition=2021','-O',str(HERE/'ExtractionRecordedC1Control.rs'),'-o',str(binary)]
        first = checks.run('ExtractionCompile',command,HERE,evidence,timeout=120)
        report['checks'].append(first)
        if first['exit_code'] == 0:
            report['executed_binary_sha256_before_run'] = sha(binary)
            second = checks.run('ExtractionControl',[str(binary)],HERE,evidence,timeout=120)
            report['checks'].append(second)
            report['executed_binary_sha256_after_run'] = sha(binary)
            assert report['executed_binary_sha256_before_run'] == report['executed_binary_sha256_after_run']
    report['status'] = 'PASS_SCOPED_ONLY' if len(report['checks']) == 2 and all(c['exit_code']==0 for c in report['checks']) else 'FAIL'
    (evidence/'ExtractionReport.json').write_text(json.dumps(report,indent=2)+'\n')
    print(evidence)
    return 0 if report['status'] == 'PASS_SCOPED_ONLY' else 1

if __name__ == '__main__': raise SystemExit(main())
