#!/usr/bin/env python3
"""Unproved COST PROBE: read-only fixture equality and retained artifact manifest."""
import hashlib, json, os, stat, sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r0-cost-probe-20261009'
base=Path('/home/dombarker/project-offloads/aspis-r0-re4-20261009/results/r0-e2e-20261009/re4')
def digest(p):
    return {'path':str(p), 'sha256':hashlib.sha256(p.read_bytes()).hexdigest(), 'size_bytes':p.stat().st_size}
def emit(name,value):
    p=out/name
    assert not p.exists(), f'evidence already exists: {p}'
    p.write_text(json.dumps(value,indent=2)+'\n')
if sys.argv[1]=='equality':
    rows=[]
    for variant in ['transfer','withdrawal']:
        for suffix in ['proof.bin','public.bin']:
            actual=out/'fixtures'/f'{variant}.{suffix}'
            reference=base/'fixtures'/actual.name
            rows.append({'variant':variant,'kind':suffix,'probe':digest(actual),'S4':digest(reference),'bitwise_equal':actual.read_bytes()==reference.read_bytes()})
    actual=json.loads((out/'fixtures/b-corruption-cases.json').read_text())
    reference=json.loads((base/'fixtures/corruption-cases.json').read_text())
    evidence={'label':'COST PROBE: unproved','fixtures':rows,'rejections':{'count':len(actual),'reference_count':len(reference),'identical_records':actual==reference},'native_field_bytes_and_phase_order':'asserted for both fixtures and every end-to-end rejection by r0_p1_prime test'}
    emit('b-equality.json',evidence)
    assert all(row['bitwise_equal'] for row in rows)
    assert len(actual)==len(reference)==1894 and actual==reference
elif sys.argv[1]=='artifacts':
    artifacts=[];retained_keys=[]
    for folder in ['b-elf','b-stack','fixtures','b-bin']:
        for p in sorted((out/folder).rglob('*')):
            if not p.is_file(): continue
            if 'payer' in p.name or 'keypair' in p.name:
                retained_keys.append({'path':str(p),'retained':True,'mode':oct(stat.S_IMODE(p.stat().st_mode))})
                continue
            artifacts.append(digest(p))
    emit('b-artifact-manifest.json',{'label':'COST PROBE: unproved','host':os.uname().nodename,'artifacts':artifacts,'keys_retained':retained_keys,'committed_evidence':'JSON, MD and logs only; binary/text/disassembly artifacts remain on the build host'})
else: raise SystemExit('equality|artifacts')
