#!/usr/bin/env python3
"""Receipt/source integrity only, not an independent privacy or Lean certificate replay."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r29-beta-uniform'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
assert not any('keypair'in n or n.endswith(('.so','.regs','.insns'))for n in manifest)
receipt=json.loads((e/'receipt.json').read_text());assert not receipt['full_privacy']and not receipt['verifier_changed']and not receipt['source_challenges_changed']
control=json.loads((root/'evidence/r28-h1-relation-capacity/affine/r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
for label,count in [('affine',184),('capacity',185)]:
    m=json.loads((e/label/'r18-stage.json').read_text());assert len(m['files'])==count and m['r29_beta_uniform']['old_G_audit_retained']
    assert receipt['stages'][label]['manifest_sha256']==sha(e/label/'r18-stage.json')
    allowed=[ex+'r17_c1_witness_audit.rs']+([ex+'performance-host/Cargo.toml']if label=='capacity'else[])
    for n,h in control['files'].items():
        if n not in allowed:assert m['files'][n]==h,n
    for n,h in m['files'].items():
        path=e/label/'source'/n
        if path.exists():assert sha(path)==h,n
    for log in ['compile','world0','world1']:
        text=(e/label/(log+'.log')).read_text();assert '\tExit status: 0'in text and '\tSwaps: 0'in text
    for w in range(2):
        log=(e/label/f'world{w}.log').read_text()
        if label=='affine':
            for s in ['R28_H1_WITNESS_JOINT ordinary_first_all7_zero=true rank=545 equations=568',
                'R29_G_WITNESS_JOINT equations=633 rank=607 beta_polynomial_coefficients_zero=true',
                'R19_CHANNEL_WITNESS source_p0_p2_retained=true first_relation_all7=true combined_final256=true decoder_independent=true',
                'R17_C1_WITNESS_VALIDATED same_public=true opposite_selected_input=true actual_helper_rebuilt=true']:
                assert s in log,s
            assert 'R17_PUBLIC_PREFIX_ACCEPTED'in(e/label/f'audit-world{w}.log').read_text()
        else:
            assert 'target_basis=276 original_equations=174708 source_rechecks=276 negative_controls=276 beta_in_matrix=false source_prefix_substituted=false'in log
            cert=json.loads((e/label/f'world{w}/certificate.json').read_text());assert cert['rank']==607 and cert['target_directions']==276 and cert['bytes']==276*1022*16
            assert not cert['beta_in_matrix']and not cert['universal_source_theorem']
            assert sha(e/label/f'world{w}/prefix.bin')==control['r28_h1_capacity']['prefixes'][w]['prefix_sha256']
    if label=='capacity':assert sha(root/'tools/r29_g_capacity.rs')==m['files'][ex+'r29_g_capacity.rs']
# Preserve the preceding 626-row source function exactly under a new name.
old=(root/'evidence/r28-h1-relation-capacity/affine/source'/ex/'r17_c1_witness_audit.rs').read_text()
start=old.index('fn r17_g_witness_audit(');end=old.index('// First affine helper step only:',start)
retained=old[start:end].replace('fn r17_g_witness_audit(','fn r19_g_witness_audit_reference(',1)
new=(e/'affine/source'/ex/'r17_c1_witness_audit.rs').read_text();assert retained in new
proofs=['0f90e0670d5c7cedf1bea159640016eeec1574ac0de89dc94d83dd9255f07da7','ca868e8f9495e06368ecaa712486befecbfaadc6ab38e8caddf38e368134ca71']
assert [f['proof-1.bin']for f in receipt['stages']['affine']['fixtures']]==proofs
for label,leaf,count in [('lean','BetaUniformCorrection.lean',7),('basis-lean','CompatibleTargetBasis.lean',3)]:
    m=json.loads((e/label/'metadata.json').read_text());assert m['exit']==0 and m['source_sha256']==sha(root/'lean/AspisV8R19'/leaf)
    log=(e/label/'compile.log').read_text();assert log.count('depends on axioms:')==count and 'sorryAx'not in log and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'actual_source_prefixes':2,'G_rank':607,'compatible_target_directions':276,'directions_checked_total':552,'lean_leaves':10,'beta_zero_not_excluded':True,'universal_source_coverage_proved':False,'full_privacy':False,'verifier_changed':False,'one_million_CU_gate':'unchanged/open'},indent=2))
