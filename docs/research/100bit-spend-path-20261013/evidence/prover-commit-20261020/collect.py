#!/usr/bin/env python3
"""Summarize retained extraction receipts; never launches or retries a job."""
import ast, hashlib, json, subprocess
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
REV='6bb2b9cb1f2517b51763ed09b16b8716d3226caa'
pins=json.loads((D/'source-pins.json').read_text())
for entry in pins['sources']:
    rel=entry['path'].split('/src/',1)[1]
    data=(ROOT/rel).read_bytes()
    assert hashlib.sha256(data).hexdigest()==entry['sha256'],rel
for name in ['extract.py','capped.py','collect.py']:
    ast.parse((D/name).read_text())
rows=[]
for name in ['salts-charon','salts-aeneas']:
    receipt=json.loads((D/name/'receipt.json').read_text())
    rows.append(dict(kind='source-extraction',attempt=name,source_revision=REV,
        module=None,lean_attempt=None,source_sha256=pins['sources'][0]['sha256'],
        deps_fingerprint=None,dependency_pins='source-pins.json',
        exit=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],
        peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],
        command=receipt['command'],limits=receipt['limits'],
        axioms=[],axioms_status='not applicable: no Lean generated or compiled',
        stdout=name+'/stdout.log',stderr=name+'/stderr.log',time=name+'/time.log'))
(D/'attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
artifacts={str(p.relative_to(D)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
           for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
manifest=dict(schema='focused-extractor-proof-packet-v1',source_revision=REV,
    status='blocked-on-translation',branch='codex/cx-prover-commit-20261020',
    frozen_verifier='b2727acd3',scope='Actual prover derive_private_salts cone; no production changes',
    blocker={'source':'crates/aspis-r1-cost-probe/src/prover.rs:191-195',
      'compiler':'interp/InterpAbs.ml:191','diagnostic':'Unexpected',
      'stage':'loop fixed-point context joining / convert_value_to_abstractions',
      'exit':2,'memory_failure':False},
    lean={'environment':'J','reserved_attempt_range':[8100,8399],'attempts_used':[],
      'new_modules':[],'changed_roots':[],'axioms':'N/A; no generated Lean or proof claims'},
    discharged_checklist_rows=[],llbc=json.loads((D/'llbc-pin.json').read_text()),
    attempts=rows,artifacts=artifacts)
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Verified source pins and Python syntax; wrote 2 extraction receipts; no Lean attempts.')
