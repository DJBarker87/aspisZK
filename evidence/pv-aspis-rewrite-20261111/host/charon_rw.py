#!/usr/bin/env python3
"""pv-aspis-rewrite-20261111: Charon on the rewritten source with the CLIENT build configuration.
Derived from pv-combined-20261111 tools/charon_roots.py (same Charon binary 0.1.223 by hash, preset, MIR level,
sysroot, include list, cargo arguments). Differences: the source root is this job's tree (branch future-version plus
the rewrites), and the client lock file is the branch's (hash recorded, not asserted against the pin's).
usage: charon_rw.py ROOT DEST TARGET_DIR [--opaque ITEM]...   (start roots: one per line in $PV_ROOTS_FILE)"""
from pathlib import Path
import subprocess, os, sys, hashlib, json
R = Path(sys.argv[1]).resolve(); dest = sys.argv[2]; tdir = sys.argv[3]
opq = [sys.argv[i + 1] for i, a in enumerate(sys.argv) if a == '--opaque']
CHARON = '/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon'
assert hashlib.sha256(open(CHARON, 'rb').read()).hexdigest() == 'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert hashlib.sha256(open(CHARON + '-driver', 'rb').read()).hexdigest() == 'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'
LOCK = R / 'tools/r1-cost-probe/Cargo.lock'
lock_before = hashlib.sha256(LOCK.read_bytes()).hexdigest()
cmd = [CHARON, "cargo", "--preset", "aeneas", "--mir", "built", "--sysroot", "default"]
for r in [l.strip() for l in open(os.environ["PV_ROOTS_FILE"]) if l.strip() and not l.startswith('#')]:
    cmd += ['--start-from-if-exists', r]
for c in ['aspis_core', 'aspis_statement', 'aspis_prover', 'aspis_z4b_probe',
          'aspis_r0_writer_copies', 'aspis_r0_block_writer_copies', 'aspis_r0_poseidon_copy']:
    cmd += ['--include', c]
for o in opq:
    cmd += ['--opaque', o]
cmd += ['--dest-file', dest, '--', '--manifest-path', str(R / 'tools/r1-cost-probe/Cargo.toml'),
        '-p', 'aspis-r1-cu-probe', '-p', 'aspis-r1-cost-probe', '--features', 'aspis-r1-cu-probe/r1p-check',
        '--offline', '--locked', '--release', '--lib', '--jobs', '4']
env = dict(os.environ, CARGO_TARGET_DIR=tdir)
src = hashlib.sha256()
for p in sorted(list((R / 'crates').rglob('*.rs')) + list((R / 'docs').rglob('*.rs'))):
    src.update(str(p.relative_to(R)).encode()); src.update(hashlib.sha256(p.read_bytes()).digest())
print(json.dumps(dict(cmd=cmd, cwd=str(R), extra_opaque=opq, client_lock_sha256=lock_before, CARGO_TARGET_DIR=tdir,
                      source_rs_digest=src.hexdigest())), flush=True)
rc = subprocess.run(cmd, cwd=R, env=env).returncode
print(json.dumps(dict(client_lock_sha256_after=hashlib.sha256(LOCK.read_bytes()).hexdigest())), flush=True)
raise SystemExit(rc)
