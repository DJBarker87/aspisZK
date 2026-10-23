#!/usr/bin/env python3
"""Audit actual typed copy+implicit cleanup composition; never whole S2."""
from pathlib import Path
import json,hashlib,re,subprocess,tempfile
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-implicit-copy-cleanup-composed'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,d in load(P/'manifest.json')['files'].items():assert sha(P/name)==d,name
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc'] for p in P.rglob('*'))
q=load(P/'qualification.json');assert len(q['targets'])==2
for tag,row in q['targets'].items():
 assert not row['accepted'] and row['receipt']['exit_status']==1 and row['receipt']['swaps']==0
 i=load(P/(tag+'-input.json'));assert sha(P/'sources'/row['source']/'src/lib.rs')==i['source_sha256']==row['source_sha256']
 assert all(load(P/(tag+'-dependency-postcheck.json'))['unchanged'].values())
 log=(P/'receipts'/tag/'stdout.log').read_text()
 if tag.endswith('v1'):assert 'does not have a corresponding `#[proof_for_contract]` harness' in log
 else:assert 'TIMEOUT' in log or 'timed out' in log or 'Timeout' in log
print(json.dumps(dict(accepted=0,excluded=2,composition_proved=False,native_sdk_closed=False)))
