#!/usr/bin/env python3
"""Offline integrity checks for the saved R391 focused result."""
import hashlib, json, pathlib, re
root=pathlib.Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
# Exact generator outputs survive and adapted compile copies differ only by imports.
for name, expected in [('Types.lean','e1c3bb14b0e5a309c165973e3f1dd866889334ee2592993c8d9c5b76678120ce'),('Funs.lean','f53f5b16d2316b790e7bf21ce739912b41d4e9fd08f1ff3bc4ce2c4f69541076')]:
    generated=root/'generated-source/AspisR388ReduceU62'/name
    assert sha(generated)==expected,(name,sha(generated))
    adapted=(root/'AspisR388ReduceU62'/name).read_text()
    original=generated.read_text()
    assert original.count('import Aeneas\n')==1
    assert adapted.count('import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')==1
    assert adapted.replace('import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n','import Aeneas\n')==original
# Verify pinned source dependency copies.
for rel, expected in [
 ('provenance/lean-dependencies/AspisR156FullFreeze/FunsCore.lean','5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2'),
 ('provenance/lean-dependencies/AspisV8R19/R161WrappedMulExecution.lean','e69b65ff69d78a399280ff098ade6968e2d399cc897be2f414dc0dcab84a7992')]:
 assert sha(root/rel)==expected,(rel,sha(root/rel))
# NUC audit explicitly binds the R161/R156 source and cached object hashes.
a=json.loads((root/'source-cache-audit.json').read_text())
assert a['status']=='read-only R391 NUC source/cache identity audit'
assert a['remote_records']['R161WrappedMulExecution']['source_sha256']=='e69b65ff69d78a399280ff098ade6968e2d399cc897be2f414dc0dcab84a7992'
assert a['remote_records']['R161WrappedMulExecution']['olean_exists'] is True
assert a['remote_records']['R156FunsCore']['source_sha256']=='5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2'
assert a['remote_records']['R156FunsCore']['olean_exists'] is True
assert 'R161WrappedMulExecution' not in a['historical_receipt_basis']['direct_local_import_map']
# All six remote attempts, including failed attempts, remain paired with raw logs.
for rid in ['1790956559884745000','1790956913622376000','1790956927857955000','1790957083954699000','1790957281547861000','1790957475592362000']:
    base=root/'.r21-scratch'/f'aspis-focus-{rid}'
    receipt=json.loads(base.with_suffix('.receipt.json').read_text())
    log=base.with_suffix('.log').read_text()
    assert str(receipt['exit_status']) in log or 'Command exited with non-zero status' in log
    assert receipt['resources']['MemorySwapMax']==0 and receipt['resources']['MemoryMax']=='7G'
# Final successful log and receipt must agree on exit and all six axiom reports.
rid='1790957475592362000'; base=root/'.r21-scratch'/f'aspis-focus-{rid}'
r=json.loads(base.with_suffix('.receipt.json').read_text()); log=base.with_suffix('.log').read_text()
assert r['exit_status']==0 and 'Exit status: 0' in log
for name in ['AspisR388ReduceU62.aspis_core.field.reduce_u64','AspisR388ReduceU62.aspis_core.field.M31.reduce_u62','generated_reduce_u64_eq_frozen','generated_reduce_u62_eq_frozen','generated_reduce_u62_success','generated_reduce_u62_encode']:
    assert name in log,name
assert (root/'AspisV8R19/R391ReduceU62Execution.lean').read_bytes()==(root/'.r21-scratch'/f'aspis-focus-{rid}.source.lean').read_bytes()
# Audit complete reports, not just declaration-name presence.
reports=re.findall(r"'([^\n]+)' depends on axioms: \[([\s\S]*?)\]",log)
assert len(reports)==6
for declaration, axioms in reports:
    assert set(x.strip() for x in axioms.split(','))=={'propext','Classical.choice','Quot.sound'},(declaration,axioms)
assert 'sorryAx' not in log and 'error:' not in log
review=json.loads((root/'lead-review.json').read_text())
assert review['complete_print_axioms']==r['complete_print_axioms']
assert review['source_sha256']==sha(root/'AspisV8R19/R391ReduceU62Execution.lean')
for rel,expected in review['promoted_sources'].items():
    assert sha(root/rel)==expected
cache=json.loads((root/'source-cache-audit.json').read_text())
for key in ['R161WrappedMulExecution','R156FunsCore']:
    row=cache['remote_records'][key]
    assert row['source_exists'] and row['olean_exists']
    assert row['source_sha256']==sha(root/row['portable_copy_path'])
    assert len(row['olean_sha256'])==64 and row['olean_size']>0
for line in (root/'SHA256SUMS').read_text().splitlines():
    expected,rel=line.split('  ',1)
    assert sha(root/rel)==expected,rel
print('R391 saved-evidence integrity: PASS')
