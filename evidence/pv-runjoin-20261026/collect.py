#!/usr/bin/env python3
"""Read-only collection of focused proof receipts; never starts a build."""
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
DEST = pathlib.Path(__file__).resolve().parent
HOST = 'dombarker@100.108.41.90'
REMOTE = '/home/dombarker/project-offloads/aspis-joint-20261019'
T = '/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for attempt, module, revision in zip(sys.argv[1::3], sys.argv[2::3], sys.argv[3::3]):
    local = ROOT / 'docs/research/v8-r0-zk-20261009/lean' / (module + '.lean')
    source = local.read_bytes()
    snap = DEST / f'{attempt}-{module.split("/")[-1]}.lean.txt'
    snap.write_bytes(source)
    logs = {}
    for kind, remote in [('out',f'{T}/out-{attempt}.log'), ('time',f'{T}/time-{attempt}.log'),
                         ('sha',f'{T}/sha-{attempt}.txt')]:
        raw = subprocess.check_output(['ssh',HOST,'cat',remote])
        (DEST / f'{kind}-{attempt}.log').write_bytes(raw)
        logs[kind] = raw.decode()
    digest = hashlib.sha256(source).hexdigest()
    assert logs['sha'].split()[0] == digest
    imports = [line.split()[1] for line in source.decode().splitlines() if line.startswith('import ')]
    dep_hashes = {}
    for dep in imports:
        path = dep.replace('.','/')
        dep_hashes[dep] = subprocess.check_output(['ssh',HOST,'sha256sum',
            f'{REMOTE}/objects/{path}.olean',f'{REMOTE}/sources/{path}.lean']).decode().splitlines()
    fingerprint = hashlib.sha256(json.dumps(dep_hashes,sort_keys=True).encode()).hexdigest()
    axioms = [line for line in logs['out'].splitlines() if 'depends on axioms:' in line or 'does not depend on any axioms' in line]
    receipt = dict(attempt=int(attempt),target=module,source_revision=revision,
        source_sha256=digest,dependency_fingerprint=fingerprint,direct_dependencies=dep_hashes,
        command=f'sh /home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh {attempt} {module} J 7000 8',
        caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128,LeanM=7000),
        axioms=axioms,exit=[s for s in logs['out'].splitlines() if s.startswith('exit=')],
        time=[s.strip() for s in logs['time'].splitlines() if any(k in s for k in ['Elapsed','Maximum resident','Swaps:','Exit status:'])],
        source_snapshot=snap.name)
    (DEST / f'receipt-{attempt}.json').write_text(json.dumps(receipt,indent=2)+'\n')
