#!/usr/bin/env python3
"""Post-run integrity comparison for an existing r18_replay output directory.

Does not execute transactions or copy/print key files. Writes a content-hash
report and verifies the driver's byte-comparison receipt.
"""
from pathlib import Path
import argparse, hashlib, json

sha = lambda b: hashlib.sha256(b).hexdigest()
p = argparse.ArgumentParser()
p.add_argument('run_dir', type=Path)
p.add_argument('--report', type=Path)
a = p.parse_args()
root=a.run_dir.resolve()
report=a.report.resolve() if a.report else root/'candidate-checkpoint-hashes.json'
if report.exists(): raise SystemExit(f'refusing existing report: {report}')
comparison=json.loads((root/'comparison.json').read_text())
manifest=json.loads((root/'input-manifest.json').read_text())
assert comparison.get('both_admitted_pairs_accepted') is True
assert comparison.get('checkpoint_equal') is True
assert comparison.get('asr8_equal') is True
assert comparison.get('initial_images_equal') is True
assert comparison.get('setup_cu_included') is False
assert manifest['proof_sha256']=='8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62'
assert manifest['public_sha256']=='72f067d263af326b017284579f30e3da7c843c6cbb29f1c6df94c8afbb1f2172'

def record(side, stage):
    d=root/side
    j=json.loads((d/f'{stage}.json').read_text())
    assert j['error'] is None, (side,stage,j.get('error'))
    return j

runs={s:{st:record(s,st) for st in ('stage1','stage2')} for s in ('before','after')}
for side in ('before','after'):
    one=runs[side]['stage1']['instruction']['accounts']
    two=runs[side]['stage2']['instruction']['accounts']
    assert len(one)==3 and [x['writable'] for x in one]==[False,False,True]
    assert all(not x['signer'] for x in one)
    assert len(two)==7 and all(not x['writable'] and not x['signer'] for x in two)
    assert len(set(x['key'] for x in one))==3
    assert len(set(x['key'] for x in two))==7
    assert (root/side/'stage1.instruction.bin').read_bytes()==bytes([3,10])
    assert len((root/side/'stage2.instruction.bin').read_bytes())==320
    assert runs[side]['stage1']['instruction']['data_sha256']
    assert runs[side]['stage2']['instruction']['data_sha256']

files={}
for side in ('before','after'):
    for rel in ('checkpoint.bin','stage2.return.bin','initial-accounts.json','expected-asr8.bin'):
        path=(root/side/rel) if rel!='expected-asr8.bin' else root/rel
        data=path.read_bytes()
        files[f'{side}/{rel}']={'bytes':len(data),'sha256':sha(data)}
assert files['before/checkpoint.bin']==files['after/checkpoint.bin']
assert files['before/checkpoint.bin']['bytes']==1768
assert files['before/stage2.return.bin']==files['after/stage2.return.bin']
assert files['before/initial-accounts.json']==files['after/initial-accounts.json']
assert files['before/stage2.return.bin']==files['expected-asr8.bin']
assert files['before/stage2.return.bin']['bytes']==792
result={
 'scope':'post-run checkpoint/result integrity only; no replay performed',
 'source_revision':manifest['harness_source_revision'],
 'harness_source_sha256':manifest['harness_source_sha256'],
 'before_source_revision':manifest['before_source_revision'],
 'after_source_revision':manifest['after_source_revision'],
 'before_elf_sha256':manifest['before_elf_sha256'],
 'after_elf_sha256':manifest['after_elf_sha256'],
 'proof_sha256':manifest['proof_sha256'],'proof_bytes':124343,
 'public_sha256':manifest['public_sha256'],'public_bytes':1880,
 'routing':{'stage1_account_count':3,'stage1_writable':[False,False,True],
            'stage2_account_count':7,'stage2_all_readonly_nonsigner':True},
 'runs':{s:{st:{'error':runs[s][st]['error'],'compute_units':runs[s][st]['compute_units'],
                 'return_data_sha256':runs[s][st]['return_data_sha256']} for st in ('stage1','stage2')} for s in ('before','after')},
 'artifacts':files,
 'driver_comparison_sha256':sha((root/'comparison.json').read_bytes()),
 'result':'PASS: checkpoint bytes and ASR8 bytes equal across the recorded before/after pair'
}
report.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'report':str(report),'checkpoint_sha256':files['before/checkpoint.bin']['sha256'],
                  'asr8_sha256':files['before/stage2.return.bin']['sha256'],'result':result['result']},indent=2))
