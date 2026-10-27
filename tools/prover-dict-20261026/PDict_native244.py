"""Ten distinct pure native contracts, sequential in one admitted scope.

Uses the existing unchanged host-run receipt helper. Does not admit, launch,
cap, lock, monitor or repair infrastructure. A refusal runs no Kani and is not
charged. The caller must honor the cross-stream quiet window and reservation.
"""
from pathlib import Path
import hashlib, json, subprocess, sys

cases = [
    'error_os_projection_retains_code',
    'error_result_reserve_branch',
    'formatter_write_safe_quotient',
    'formatter_two_writes_shared_sink',
    'from_fn_m31',
    'from_fn_qm31',
    'from_fn_wide',
    'coefficients_m31',
    'coefficients_qm31',
    'coefficients_wide',
]
proof = Path('tools/prover-dict-20261026/proof-world244')
pins = {str(p):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in proof.iterdir() if p.suffix in ('.rs','.toml','.lock')}
pins[__file__] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
start = int(sys.argv[1]) if len(sys.argv)>1 else 1
end = int(sys.argv[2]) if len(sys.argv)>2 else len(cases)
summary = Path('receipts/pdict244-kani-summary.json')
rows = json.loads(summary.read_text()) if summary.exists() else []
for number, case in enumerate(cases, 1):
    if number < start or number > end: continue
    label = f'pdict244-kani-{number:03d}'
    if number == start and len(sys.argv)>3: label += sys.argv[3]
    cmd = ['timeout','120','cargo','kani','--manifest-path',str(proof/'Cargo.toml'),
           '--lib','--harness',f'native::{case}','--exact','--solver','kissat',
           '-j','4','--output-format','terse']
    print(label,case,flush=True)
    ret = subprocess.run([sys.executable,'tools/prover-rw-20261023/host-run.py',
                          label,*cmd]).returncode
    folder = Path('receipts')/label
    if not (folder/'receipt.json').exists():
        print('No completed receipt; stop this batch for admission/infrastructure review.',flush=True)
        break
    (folder/'input-supplement.json').write_text(json.dumps(dict(
        authorization_base='dfd8a438bc10509be652365de65ea98566d13725',
        proof_inputs=pins,command=cmd,exit=ret,
        statement_qualification='Pure native projections and bounded array/sink contracts only. '
            'No syscalls, stubs, disabled checks, native OS world or universal Drop claim.',
        expected_work='Compilation with opt-level3, then the named Kani contract; no arithmetic elimination.',
        scope_qualification='Sequential contracts share one 6G/8G/swap0/Tasks64 scope. '
            'GNU time is per command; cgroup peak is cumulative.',
        ambient_revision_qualification='The historical snapshot label in the raw runner is retained. '
            'These exact proof-only inputs supplement its production-source inventory.'),indent=2)+'\n')
    rows.append(dict(label=label,harness=case,exit=ret))
    stderr=(folder/'stderr.log').read_text()
    if 'error[E' in stderr or 'could not compile' in stderr or 'aborting due to' in stderr:
        print('Compilation failed; isolate/change the source before another Kani launch.',flush=True)
        break
Path('receipts/pdict244-kani-summary.json').write_text(json.dumps(rows,indent=2)+'\n')
