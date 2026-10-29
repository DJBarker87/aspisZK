from pathlib import Path
import json,hashlib,re,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;I=E/'NEB_IMPORTED_SCALAR';sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
sys.path[:0]=[str(E.parent/'native-ledger3-20261029'),str(E.parent/'native-ledger2-20261028')]
import NDT_review
from NEB_patch_value import replay
M=obj(E/'NEB_SCALAR_IMPORTS.json')
for f in M['files']:
 raw=(R/f['path']).read_bytes();assert sha(raw)==f['sha256'];assert raw==subprocess.check_output(['git','show',M['revision']+':'+f['source_path']],cwd=R)
lock=sha(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],cwd=R));kmx=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes());checks=[]
for n,exitcode in [(1,0),(2,1),(3,0),(4,1),(11,0),(12,1)]:
 a=f'NDH_K{n:03}';d=obj(I/a/'receipt.json');g=obj(I/(a+'-graph-check.json'));l=obj(I/(a+'-lock-check.json'));log=(I/a/'stdout.log').read_text();assert d['exit_status']==exitcode and d['swaps']=='0'
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert d['copy_patch_sha256']==kmx and l==dict(before=lock,after=lock,unchanged=True)
 assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'] and not g['edge_errors'] and not g['new_package_tuples']
 NDT_review.check_features(g,'library-helper');assert not obj(I/(a+'-source-check.json'))['errors']
 assert re.findall(r'\*\* (\d+) of \d+ failed',log)[-1]==str(exitcode)
 if n==4:assert 'NDH_native::reference::table_ref(value)) != true' in log.split('Failed Checks:')[1] and 'fast_domain::table_value::' in log.split('Failed Checks:')[1]
 if n==12:assert '(* r == self.0) != true' in log.split('Failed Checks:')[1] and 'FibreIndex::get::' in log.split('Failed Checks:')[1]
 patched=replay((I/a/'NDH_harness.patch').read_text(),R)
 for f,h in d['source_hashes'].items():
  if f.startswith('NDH_src/') and f[8:] in patched:assert sha(patched[f[8:]])==h,(a,f)
 checks.append(dict(attempt=a,receipt_sha256=sha((I/a/'receipt.json').read_bytes()),exit_status=exitcode,wall_seconds=d['wall_seconds'],peak_rss_kib=d['peak_rss_kib'],swaps=d['swaps']))
# Native table source is exactly the transparent context, not a copied helper.
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/fast_domain.rs'],cwd=R).decode()
assert re.search(r'fn table_value\(value: \(u32, u32\)\) -> CM31 \{\s*CM31::new\(M31\(value\.0\), M31\(value\.1\)\)\s*\}',frozen)
source=replay((I/'NDH_K003/NDH_harness.patch').read_text(),R)['crates/aspis-r1-cost-probe/src/NDH_table.rs'].decode()
assert 'fn table_contract(){let a:u32=kani::any();let b:u32=kani::any();table_value((a,b));}' in source
assert 'kani::assume' not in source and 'stub_verified' not in source and 'kani::stub' not in source
ex=obj(I/'NDH_E001/NDH_EXTRACTION_PINS.json');assert obj(I/'NDH_E001/receipt.json')['exit_status']==0
assert ex['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and ex['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert ex['rust_reference_sha256']==sha(replay((I/'NDH_K003/NDH_harness.patch').read_text(),R)['crates/aspis-r1-cost-probe/src/NDH_reference.rs'])
out=dict(schema='NEB-scalar-table-native-review-v1',source_revision=M['revision'],native_results=checks,copy_patch_sha256=kmx,table_domain='All raw u32 pairs, no requires/assume; actual CM31::new executes',constructor_native_association='TRANSPARENT_EXECUTED_CONTEXT: table_value((a,b)) returns actual CM31::new(M31(a),M31(b)) unchanged. Arbitrary pair covers every constructor input; raw native K003/K004, not a composed-parent assumption. No Kani constructor stub or source-copy replacement.',getter_domain='Valid same private index <262144; scalar result unchanged',copy_dependency='Only scalar/tuple/record operations in selected value roots; approved KMX present and K001/K002 controls paired; no reached source slice/array copy/clone/Vec in these roots',function_pointer_dependency=False,trust='Approved NativeContractSemanticTransport option A reclassification, never removal',new_native_attempts=0)
p=E/'NEB_SCALAR_REVIEW.json'
if '--check' in sys.argv:assert obj(p)==out
else:p.write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(native_receipts=len(checks),new_native_attempts=0,constructor_context='all raw pairs',composed_credit_from_review_alone=0)))
