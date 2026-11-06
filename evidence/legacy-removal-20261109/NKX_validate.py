"""Final source boundaries, all retained pair files, deleted-symbol and size gates."""
from NKX_source import *
import re
subprocess.run([sys.executable,str(E/'NKX_source.py')],check=True,cwd=R)
x=json.loads((E/'NKX_BYTE_IDENTITY.json').read_text())
assert subprocess.run(['git','diff','--quiet',F,'--','crates','programs/r1-cost-probe','Cargo.lock'],cwd=R).returncode==0
unchanged=[]
for p in (R/'programs/aspis-pool/src').glob('pair*.rs'):
 rel=str(p.relative_to(R));assert p.read_bytes()==frozen(rel),rel
 unchanged.append(dict(path=rel,sha256=sha(p.read_bytes())))
all_paths=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'programs/aspis-pool'],cwd=R,text=True).splitlines()
source_manifest={str(p.relative_to(R)):sha(p.read_bytes()) for p in (R/'programs/aspis-pool').rglob('*') if p.is_file()}
lock=(R/'Cargo.lock').read_bytes();assert lock==frozen('Cargo.lock')
dispatch=funcs('programs/aspis-pool/src/processor.rs',(R/'programs/aspis-pool/src/processor.rs').read_bytes())['programs/aspis-pool/src/processor.rs::process_instruction']['text']
for magic in [b'ASIN',b'ASDI',b'ASPT',b'ASWD',b'ASPP',b'ASPF',b'ASPX']:
 assert magic not in dispatch
for name in ['process_initialize_with_runtime_v1','process_deposit_with_runtime_v1','process_private_transfer_with_runtime_v1','process_withdrawal_with_runtime_v1','process_prepare_settlement_with_runtime_v1','process_settle_prepared_with_runtime_v1','process_cancel_prepared_settlement_with_runtime_v1']:
 assert name not in (R/'programs/aspis-pool/src/processor.rs').read_text()
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not list(E.rglob('__pycache__'))
(E/'NKX_SOURCE_VALIDATION.json').write_text(json.dumps(dict(status='PASS',frozen_revision=F,protected_diff_empty=True,cargo_lock_sha256=sha(lock),source_manifest=source_manifest,pair_files_byte_identical=unchanged,retained_function_exceptions=x['changed_functions'],source_added_dependencies=x['source_added_dependencies'],tree_sitter='0.25.2',tree_sitter_rust='0.24.2',print_axioms='N/A: no Lean/extraction/Kani'),indent=1)+'\n')
(E/'NKX_DIFF.patch').write_bytes(subprocess.check_output(['git','diff',F,'--','programs/aspis-pool'],cwd=R))
print('NKX source boundaries and byte identity: PASS')
