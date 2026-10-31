#!/usr/bin/env python3
"""Revalidate the exact reducer native contract, controls and source erasure."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path[:0]=[str(E.parent/'native-ledger3-20261029'),str(E.parent/'native-ledger2-20261028')]
import NDT_review
sha=lambda b:hashlib.sha256(b).hexdigest()
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',F+':'+p],cwd=R)
def load(p):return json.loads(p.read_text())
patch=E/'NEB_reducer.patch';restored=NDT_review.restore_patch(patch.read_bytes(),frozen)
field='crates/aspis-core/src/field.rs';helper='crates/aspis-core/src/field/NEB_reducer.rs'
assert restored[helper]==(E/'NEB_reducer.rs').read_bytes()
# Remove exactly the added cfg(kani) attributes/module declaration, then demand
# byte identity of the entire frozen field file, not merely selected bodies.
erased=restored[field].decode().replace('#[cfg_attr(kani,kani::ensures(|r| NEB_reducer::reduce_post(x,*r)))]\n','').replace('    #[cfg_attr(kani,kani::ensures(|r| NEB_reducer::wrapper_post(value,*r)))]\n','').removesuffix('\n#[cfg(kani)] #[path="field/NEB_reducer.rs"] mod NEB_reducer;\n')
assert erased.encode()==frozen(field)
helpertext=restored[helper].decode();start=helpertext.index('pub fn reference');end=helpertext.index('\npub fn reduce_post',start)
assert (E/'NEB_reference.rs').read_text()=='const P:u32=0x7fff_ffff;\n'+helpertext[start:end]+'\n'
assert not any(x in helpertext for x in ['copy_from_slice','copy_nonoverlapping','to_vec','Vec<','Option<fn','unsafe'])
D=load(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');lock=sha(frozen('Cargo.lock'));kmx=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
results=[];graph_hashes=set()
expected=[('NEB_K001','reduce_contract',0,None),('NEB_K002','reduce_contract',1,'reduce_post'),('NEB_K003','weak_contract',0,None),('NEB_K004','real_body',0,None),('NEB_K005','unimplied',1,'placeholder message'),('NEB_K006','frame_control',1,'is assignable'),('NEB_K007','wrapper_contract',0,None),('NEB_K008','wrapper_contract',1,'wrapper_post')]
for name,target,status,control in expected:
 rc=load(E/name/'receipt.json');g=load(E/(name+'-graph-check.json'));lc=load(E/(name+'-lock-check.json'));text=(E/name/'stdout.log').read_text()
 assert rc['exit_status']==status and rc['target']=='field::NEB_reducer::'+target
 assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert rc['swaps']=='0' and rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert lc==dict(before=lock,after=lock,unchanged=True)
 assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'] and not g['edge_errors'] and not g['new_package_tuples']
 assert len(g['resolved_features_all_crates'])==g['resolved_packages']==441
 assert next(r['features'] for r in g['selected_closure'] if r['name']=='aspis-core')==['r0']
 graph_hashes.add(g['canonical_graph_sha256'])
 assert not load(E/(name+'-source-check.json'))['errors']
 assert rc['source_hashes']['NEB_src/'+field]==sha(restored[field])
 assert rc['source_hashes']['NEB_src/'+helper]==sha(restored[helper])
 assert rc['copy_patch_sha256']==kmx
 assert '--locked' not in rc['native_command']
 assert 'VERIFICATION:- '+('SUCCESSFUL' if status==0 else 'FAILED') in text
 failures=re.findall(r'\*\* (\d+) of \d+ failed',text);assert failures and int(failures[-1])==(0 if status==0 else 1)
 assert not re.search(r'error\[|error: could not compile|timed out|VERIFICATION:- UNKNOWN',text)
 if control:assert control in text.split('Failed Checks:',1)[1]
 if name in ['NEB_K006','NEB_K007','NEB_K008']:assert load(E/(name+'-tool-check.json'))==load(E/'NEB_TOOL_PINS.json')
 results.append(dict(attempt=name,target=target,expected_exit=status,receipt_sha256=sha((E/name/'receipt.json').read_bytes()),wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],control=control))
assert len(graph_hashes)==1
callee='crates/aspis-core/src/field.rs::reduce_u64';caller='crates/aspis-core/src/field.rs::M31::reduce_u64'
for fn in [caller,callee]:
 row=next(r for r in D['rows'] if r['function']==fn);a,b=row['frozen_body_byte_range'];body=frozen(field)[a:b];assert sha(body)==row['frozen_body_sha256']
 assert body in restored[field]
 if fn==caller:assert re.sub(r'\s+','',body.decode())=='{M31(reduce_u64(value))}'
assert '#[kani::stub_verified(super::reduce_u64)]' in helpertext
out=dict(schema='NEB-reducer-native-review-v1',frozen_revision=F,functions=[callee,caller],native_results=results,body_erasure='entire field.rs byte identical after removing exactly two cfg(kani) ensures attributes and one cfg(kani) harness module',patch_sha256=sha(patch.read_bytes()),reference_sha256=sha((E/'NEB_reference.rs').read_bytes()),copy_stub_patch_sha256=kmx,copy_dependent=False,rule14_dependent=False,source_feature_parity='Both reached frozen bodies contain no cfg feature/target branch. Exact native core-r0 source bodies equal their deployed bodies.',fidelity=dict(inverted_ensures='NEB_K002',weak_contract='NEB_K003',real_body='NEB_K004',unimplied_under_stub='NEB_K005',modifies_violation='NEB_K006'),callsite=dict(caller=caller,callee=callee,domain='every u64, no requires clause',actual_expression='M31(reduce_u64(value))',native_proof='NEB_K007',matched_control='NEB_K008',selected_callee_positive='NEB_K001',selected_callee_control='NEB_K002',callee_reply='u32, wrapped unchanged into the sole M31 field'),composition_trust='NativeContractSemanticTransport: P6/D188 reclassification, never removal',remaining='Independent reference extraction and checked Lean reference/cohort/state/effect laws must pass before composition credit')
if '--check' in sys.argv:assert load(E/'NEB_NATIVE_REVIEW.json')==out,'native review changed; explicit regeneration/review required'
else:(E/'NEB_NATIVE_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(native_review_passed=True,attempts=len(results),composed_credit_before_Lean=0)))
