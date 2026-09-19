#!/usr/bin/env python3
"""Stage a pinned, host-only research replay; never build or run deployment code.

Copies a bounded Git source subset to a NEW directory. Restores the seven
authenticated generated inputs, including the recovered v4 performance image.
The three missing verifier/transaction-harness images are NOT substituted or
claimed recovered. They are outside the host crate's declared dependencies.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from reconstruct_generated_inputs import EXPERIMENTS, TARGET, transform_performance_v4


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    if out.exists():
        parser.error('output must not exist; existing work is never overwritten')
    source_manifest = json.loads((repo / 'docs/research/v8-full-view-zk-20260912/SOURCE_MANIFEST.json').read_text())
    revision = source_manifest['target_commit']
    out.mkdir(parents=True)
    paths = ['Cargo.toml', 'Cargo.lock', 'crates', 'programs',
             'audit/poseidon-pair-probe/program', 'xtask', str(EXPERIMENTS), str(TARGET)]
    archive = subprocess.Popen(['git', '-C', str(repo), 'archive', revision, '--', *paths], stdout=subprocess.PIPE)
    try:
        subprocess.run(['tar', '-x', '-C', str(out)], stdin=archive.stdout, check=True)
    finally:
        archive.stdout.close()
    if archive.wait() != 0:
        raise RuntimeError('pinned Git archive failed')
    generated = out / '.r15-generated'
    runner = Path(__file__).with_name('reconstruct_generated_inputs.py')
    result = subprocess.run([sys.executable, str(runner), '--repo', str(out), '--output', str(generated)])
    assert result.returncode == 2  # retained three missing preimages
    report = json.loads((generated / 'report.json').read_text())
    assert report['passes'] == 7 and report['unavailable_preimages'] == 3
    v4 = json.loads((out / TARGET / 'evidence/integration-inputs-v4.json').read_text())
    verified = []
    for check in report['checks']:
        if check['status'] != 'PASS':
            continue
        relative = Path(check['path'])
        if relative == EXPERIMENTS / 'performance.rs':
            text = transform_performance_v4((out / TARGET / 'upstream/performance.rs').read_text())
            (generated / relative).write_text(text)
        assert digest(generated / relative) == v4[str(relative)]['after']
        shutil.copyfile(generated / relative, out / relative)
        verified.append({'path': str(relative), 'sha256': digest(out / relative)})
    manifest = out / EXPERIMENTS / 'performance-host/Cargo.toml'
    metadata = {
        'source_revision': revision,
        'generated_v4_inputs': verified,
        'missing_nonhost_preimages': [c for c in report['checks'] if c['status'] != 'PASS'],
        'complete_generated_closure': False,
        'host_manifest': str(manifest),
        'rustflags': ' '.join('--cfg ' + cfg for cfg in source_manifest['host_cfgs']) + ' -A dead_code -A unexpected_cfgs',
        'features': ','.join(source_manifest['cargo_features']),
        'scope': 'stage only; no build, proof generation, deployment, network or wallet operation',
    }
    (out / 'r15-stage.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps(metadata, indent=2))


if __name__ == '__main__':
    main()
