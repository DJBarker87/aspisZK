#!/usr/bin/env python3
"""Final local nonmutating preparation audit; receipt writes only in this job."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

R = Path(__file__).resolve().parents[2]
E = R / 'evidence/port28rootexport-20261024'
T = R / 'tools/port28rootexport-20261024'

def pin(p):
    data = p.read_bytes()
    assert len(data) <= 5_000_000
    return dict(path=str(p.relative_to(R)), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))

def main():
    ast.parse((T / 'Port28ROOTEXPORT_prepare.py').read_text())
    command = ['python3', '-B', 'tools/port28rootexport-20261024/Port28ROOTEXPORT_prepare.py']
    start = time.monotonic()
    result = subprocess.run(command, cwd=R, capture_output=True)
    wall = time.monotonic() - start
    (E / 'Port28ROOTEXPORT_audit.stdout.log').write_bytes(result.stdout)
    (E / 'Port28ROOTEXPORT_audit.stderr.log').write_bytes(result.stderr)
    assert result.returncode == 0, result.stderr.decode()
    summary = json.loads(result.stdout)
    assert summary['exact_spans'] == 14 and summary['source_seed_names'] == 67
    assert summary['new_lean_invocations'] == summary['host_accesses'] == 0
    observed_at = datetime.now(timezone.utc).isoformat()
    ps_command = ['ps', '-p', '94997', '-o', 'pid=,lstart=,stat=,comm=']
    ps = subprocess.run(ps_command, capture_output=True)
    # Absence is only an observation, never an inferred start/terminal identity.
    gate = dict(command=ps_command, observed_at=observed_at, exit_status=ps.returncode,
                stdout=ps.stdout.decode(), stderr=ps.stderr.decode(),
                recorded_start_identity=None, terminal_marker=None,
                host_gate='BLOCKED: start identity and post-exit terminal marker missing')
    (E / 'Port28ROOTEXPORT_host-gate.json').write_text(json.dumps(gate, indent=2) + '\n')
    manifest = json.loads((E / 'Port28ROOTEXPORT_manifest.json').read_text())
    assert manifest['new_object_observations'] == manifest['transports'] == manifest['emitted_declarations'] == []
    paths = subprocess.check_output(['git', 'diff', '--name-only', 'e37ef5182a83bdd1104eeec17da1f669a8c0a778'], cwd=R, text=True).splitlines()
    assert all(p.startswith(('tools/port28rootexport-20261024/', 'evidence/port28rootexport-20261024/')) for p in paths)
    # All new evidence is bounded text. Record exact input/output/tool hashes.
    files = sorted(p for folder in [E,T] for p in folder.iterdir() if p.is_file()
                   and p.name != 'Port28ROOTEXPORT_audit.receipt.json')
    u = resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt = dict(schema='Port28ROOTEXPORT-final-offline-audit-v1', command=command,
                   audit_command=['python3', '-B', 'tools/port28rootexport-20261024/Port28ROOTEXPORT_audit.py'],
                   source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
                   source_tree_dirty=True, exit_status=result.returncode, wall_seconds=wall,
                   child_peak_rss_bytes=u.ru_maxrss, swaps=u.ru_nswap, summary=summary,
                   files=[pin(p) for p in files], print_axioms='N/A: data export preparation; no theorem',
                   lean_invocations=0, host_accesses=0, historical_receipts='REUSED only, full original axiom lines in manifest',
                   status='PASS offline source preparation; BLOCKED missing launcher terminal identity/marker',
                   object_graph='not acquired', full_constantinfo_closure='not computed', duplicate_conflicts='not computed')
    (E / 'Port28ROOTEXPORT_audit.receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(exit_status=0, inputs=summary['immutable_inputs'], seeds=67, wall_seconds=wall,
                          peak_rss_bytes=u.ru_maxrss, swaps=u.ru_nswap, status=receipt['status'])))

if __name__ == '__main__':
    main()
