#!/usr/bin/env python3
"""Offline evidence validator; never launches a build or extraction."""
from pathlib import Path
import argparse, hashlib, json
OUT=Path(__file__).resolve().parents[1]
BASE=OUT.parents[1]
ROOT=BASE.parents[2]
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def assemble():
    frozen=json.loads((OUT/'frozen-source-hashes.json').read_text())
    assert frozen['source_revision']=='b2727acd3abf79315d18b754a260f58f4b1c6326'
    for f,h in frozen['files'].items(): assert sha(ROOT/f)==h,f
    validation=json.loads((OUT/'source-validation.json').read_text())
    assert validation['checked_files']==len(frozen['files']) and validation['mismatches']==[]
    runs=[]
    for phase,exit_code in [('charon',0),('aeneas',2)]:
        p=OUT/'receipts'/('extract-checkpoint-01-'+phase)/'receipt.json'
        r=json.loads(p.read_text());assert r['exit_status']==exit_code
        assert r['source_revision']==frozen['source_revision'] and r['swaps']==0
        assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
        inp=json.loads((OUT/'extraction-checkpoint-01'/(phase+'-input.json')).read_text())
        assert r['command']==inp['command']
        for f,h in inp['source_hashes'].items(): assert sha(ROOT/f)==h,f
        assert set(inp['tool_pins'].values())=={'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45','4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'}
        runs.append(r)
    log=(OUT/'receipts/extract-checkpoint-01-aeneas/stdout.log').read_text()
    assert 'Could not match the contexts' in log and '330:4-330:55' in log
    pin=json.loads((OUT/'llbc-pin.json').read_text())
    assert pin['has_errors'] is False and pin['generated_lean']==[]
    assert pin['sha256']=='ae1e3919047281d79489a386af09583ad0f562c524b5607aedca9678664a593b'
    assert not list(OUT.rglob('*.lean'))
    refs=[ROOT/'evidence/freeze-20261020/FREEZE.md',ROOT/'evidence/freeze-20261020/artifacts-sha256.txt',BASE/'design/CHECKPOINT-LOG-TX1-20261020.md',BASE/'design/TX1-FINISH-20261020.md',BASE/'evidence/stage2-continuation-20261020/proofs/resume-fact-v6/source.lean',BASE/'evidence/stage2-continuation-20261020/proofs/final-binding.json']
    return dict(schema='focused-extractor-proof-packet-v1',status='STOPPED: frozen checkpoint root borrow/context matching failure in pinned Aeneas',publication_base_revision='fa894d83d2f3ad6df34bc8493881c780621d553e',source_revision=frozen['source_revision'],modules=[],new_lean_runs=[],generated_lean=[],axioms='N/A: failed Aeneas; no Lean emission or theorem',runs=runs,llbc=pin,remaining_obligations=['R15 writer determinism and length','R15 writer/resume digest composition','G_R1.7/G_R1.9 guarded sole account write','R15 resume field recovery','P2 account ownership and provenance'],references={str(p.relative_to(ROOT)):sha(p) for p in refs},files={str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='manifest.json'})
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    raw=json.dumps(assemble(),indent=2,sort_keys=True)+'\n';p=OUT/'manifest.json'
    if a.check: assert p.read_text()==raw,'manifest differs'
    else:p.write_text(raw)
    print('PASS: pinned failure packet internally consistent; R15 remains open')
