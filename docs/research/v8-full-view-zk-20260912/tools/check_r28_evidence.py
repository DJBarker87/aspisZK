#!/usr/bin/env python3
"""Integrity/receipt audit only; does not repeat elimination or prove privacy."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r28-h1-relation-capacity'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
assert not any('keypair'in n or n.endswith(('.so','.regs','.insns'))for n in manifest)
receipt=json.loads((e/'receipt.json').read_text());assert not receipt['full_privacy']and not receipt['verifier_changed']and not receipt['source_beta_changed']
control=json.loads((root/'evidence/r27-sparse-preparation/shared/r18-stage.json').read_text())
stages={}
for label in ['capacity','affine']:
    stage=json.loads((e/label/'r18-stage.json').read_text());stages[label]=stage
    assert len(stage['files'])==184 and receipt['stages'][label]['manifest_sha256']==sha(e/label/'r18-stage.json')
    for n,h in stage['files'].items():
        source=e/label/'source'/n
        if source.exists():assert sha(source)==h,n
    for n,h in control['files'].items():
        permitted=['performance-host/Cargo.toml']+(['performance.rs','r17_c1_witness_audit.rs']if label=='affine'else[])
        if not any(n.endswith('/'+s)for s in permitted):assert stage['files'][n]==h,(label,n)
    assert '\tExit status: 0'in(e/label/'compile.log').read_text()
    for w in range(2):
        log=(e/label/f'world{w}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
        if label=='capacity':
            assert 'baseline_rank=540 augmented_rank=545 kernel_image_dimension=5 original_rows_checked=2840'in log
            assert 'corrupt_certificates_rejected=5 source_beta_changed=false full_privacy=false'in log
            assert (e/label/f'world{w}/right-inverse.bin').stat().st_size==5*1022*16
            assert (e/label/f'world{w}/targets.bin').stat().st_size==5*7*16
            prefix=stage['r28_h1_capacity']['prefixes'][w]
            assert sha(e/label/f'world{w}/prefix.bin')==prefix['prefix_sha256']
            assert sha(root/f'evidence/r27-sparse-preparation/shared/r24-host-a/world{w}.log')==prefix['capture_sha256']
        else:
            for s in ['R28_H1_WITNESS_JOINT ordinary_first_all7_zero=true rank=545 equations=568',
                'R19_G_WITNESS_JOINT equations=626 rank=602',
                'R19_CHANNEL_WITNESS source_p0_p2_retained=true first_relation_all7=true combined_final256=true decoder_independent=true',
                'R17_C1_WITNESS_VALIDATED same_public=true opposite_selected_input=true actual_helper_rebuilt=true']:
                assert s in log,s
            assert 'R17_PUBLIC_PREFIX_ACCEPTED'in(e/label/f'audit-world{w}.log').read_text()
assert sha(root/'tools/r28_h1_capacity.rs')==stages['capacity']['files']['docs/research/v8-no-work-100-20260907/experiments/r28_h1_capacity.rs']
proofs=['0f90e0670d5c7cedf1bea159640016eeec1574ac0de89dc94d83dd9255f07da7','ca868e8f9495e06368ecaa712486befecbfaadc6ab38e8caddf38e368134ca71']
assert [f['proof-1.bin']for f in receipt['stages']['affine']['fixtures']]==proofs
meta=json.loads((e/'lean/metadata.json').read_text());assert meta['exit']==0 and meta['source_sha256']==sha(root/'lean/AspisV8R19/H1RelationLift.lean')
log=(e/'lean/compile.log').read_text();assert log.count('depends on axioms:')==5 and'sorryAx'not in log and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'actual_source_prefixes':2,'H1_rank':[540,545],'explicit_directions':10,'full_source_witness_audits':2,'lean_leaves':5,'verifier_changed':False,'full_privacy':False,'one_million_CU_gate':'unchanged/open'},indent=2))
