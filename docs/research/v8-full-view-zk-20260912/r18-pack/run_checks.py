#!/usr/bin/env python3
"""Build and replay the exact finite-model checks. No network, Rust or SBF use."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import time


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-dir', type=Path, required=True,
                        help='New output directory for executables and measured checks.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    out = args.build_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    compiler = shutil.which('g++')
    if compiler is None:
        raise SystemExit('g++ with C++17 support is required.')
    report = {'scope': 'finite source-shaped arithmetic models; not actual Rust/SBF/security',
              'compiler': subprocess.check_output([compiler, '--version'], text=True).splitlines()[0],
              'builds': [], 'checks': [], 'rust_compiled': False, 'lean_compiled': False,
              'sbf_executed': False, 'full_view_privacy_proved': False}
    for name, source, extension in [('probe', 'structural_probe.cpp', False),
                                    ('probe_q', 'structural_probe.cpp', True),
                                    ('operators', 'operator_checks.cpp', True)]:
        command = [compiler, '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror']
        if extension:
            command.append('-DEXTENSION')
        command += [str(root / 'tests' / source), '-o', str(out / name)]
        started = time.monotonic()
        completed = subprocess.run(command, text=True, capture_output=True, timeout=120)
        (out / f'{name}-compile.log').write_text(completed.stdout + completed.stderr)
        if completed.returncode != 0:
            raise RuntimeError(f'{name} compile failed; inspect {out}.')
        report['builds'].append({'name': name, 'exit': 0,
                                 'seconds': round(time.monotonic() - started, 3),
                                 'assertions_enabled': True})
    cases = [
        ('sparse_original_T_M31', 'probe', ['stride3', '16', '0'], 601),
        ('sparse_original_T_QM31', 'probe_q', ['stride3', '6', '0'], 601),
        ('H1_original_T_M31', 'probe', ['h1', '8', '0'], 540),
        ('negative_first271_code_M31', 'probe', ['first271', '4', '0'], 538),
        ('negative_affine_T_H1_M31', 'probe', ['h1', '8', '1'], 517),
        ('minimal_T_H1_M31', 'probe', ['h1', '8', '2'], 540),
        ('minimal_T_G_M31', 'probe', ['stride3', '8', '2'], 601),
        ('minimal_T_H1_QM31', 'probe_q', ['h1', '2', '2'], 540),
        ('minimal_T_G_QM31', 'probe_q', ['stride3', '3', '2'], 601),
        ('operator_identities_QM31', 'operators', [], None),
    ]
    for name, executable, arguments, expected in cases:
        started = time.monotonic()
        completed = subprocess.run([str(out / executable), *arguments], text=True,
                                   capture_output=True, timeout=180)
        (out / f'{name}.log').write_text(completed.stdout + completed.stderr)
        if completed.returncode != 0:
            raise RuntimeError(f'{name} failed; inspect {out}.')
        observed = json.loads(completed.stdout)
        if expected is not None:
            assert observed['ranks'] == [expected] * int(arguments[1]), name
        else:
            assert observed['all_passed'] and observed['sparse_terminal_cases'] == 295
            assert observed['minimal_support'] == 163
        entry = {'name': name, 'seconds': round(time.monotonic() - started, 3),
                 'expected_rank': expected, 'result': observed}
        report['checks'].append(entry)
        print(json.dumps(entry), flush=True)
    report['all_asserted_checks_passed'] = True
    (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'PASS. Evidence: {out / "results.json"}')


if __name__ == '__main__':
    main()
