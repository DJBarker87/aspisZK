"""Revalidate the final committed constructor controls, without composition credit."""
from pathlib import Path
import json,hashlib,subprocess,re,sys
E=Path(__file__).resolve().parent;R=E.parent.parent;I=E/'NEB_IMPORTED_INDEX_FINAL';sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
sys.path[:0]=[str(E.parent/'native-ledger3-20261029'),str(E.parent/'native-ledger2-20261028')]
import NDT_review
from NEB_patch_value import replay
M=obj(E/'NEB_INDEX_FINAL_IMPORTS.json')
for f in M['files']:
 raw=(R/f['path']).read_bytes();assert sha(raw)==f['sha256'];assert raw==subprocess.check_output(['git','show',M['revision']+':'+f['source_path']],cwd=R)
lock=sha(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],cwd=R));kmx=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes());checks=[]
for n,exitcode in [(40,0),(41,1),(42,0),(43,1),(46,0),(47,1),(48,0),(49,1),(50,0),(51,1)]:
 a=f'NEA_K{n:03}';d=obj(I/a/'receipt.json');g=obj(I/(a+'-graph-check.json'));l=obj(I/(a+'-lock-check.json'));log=(I/a/'stdout.log').read_text()
 assert d['exit_status']==exitcode and d['swaps']=='0'
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert d['copy_patch_sha256']==kmx and l==dict(before=lock,after=lock,unchanged=True)
 assert g['exact_frozen_selected_graph'] and g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples']
 assert g['missing_package_tuples']==g['disabled_packages']==[['aspis-r1-cert-build','0.0.0',None],['aspis-r1-cert-check','0.0.0',None],['aspis-z4b-probe','0.1.0',None]]
 assert not any(p['name'] in [x[0] for x in g['disabled_packages']] for p in g['selected_closure'])
 NDT_review.check_features(g,'library-helper');assert not obj(I/(a+'-source-check.json'))['errors']
 assert re.findall(r'\*\* (\d+) of \d+ failed',log)[-1]==str(exitcode)
 patched=replay((I/a/'NEA_harness.patch').read_text(),R)
 for f,h in d['source_hashes'].items():
  if f.startswith('NEA_src/') and f[8:] in patched:assert sha(patched[f[8:]])==h,(a,f)
 if n in [41,43,47,49,51]:
  failed=log.split('Failed Checks:')[1];assert any(s in failed for s in {41:['NEA_wrong_index'],43:['is_ok()'],47:['assignable','modifies','write_set','assigns'],49:['KMX_ptr_wrong'],51:['v.get()','get() == i']}[n]),(a,failed)
 checks.append(dict(attempt=a,exit_status=exitcode,receipt_sha256=sha((I/a/'receipt.json').read_bytes())))
assert (I/'NEA_Index.lean').read_bytes()==(E/'NEB_IMPORTED/NEA_Index.lean').read_bytes()
packet=next(x for x in obj(I/'NEA_CLOSED.json') if x['function'].endswith('::FibreIndex::new'));assert packet['status']=='CLOSED-CONDITIONAL'
out=dict(schema='NEB-final-index-review-v1',revision=M['revision'],native=checks,copy_patch_sha256=kmx,shape='Result<FibreIndex, r0::Error>, usize payload and all seventeen error variants',shape_controls='inverted constructor/weak ensures fail; modifies violation fails; real-body caller passes while identical assertion under weak stub_verified fails; exact KMX copy positive/control',claim=packet,source_theorem_unchanged=True,new_native_attempts=0,composed_credit=0,remaining='Coherent geometry op12 is an abstract checked-constructor port, while the separate geometry FibreIndex carrier is a Usize alias. The accepted reference establishes exact payload erasure on u<262144. No standalone adopted constructor Result declaration has been located. Do not invent indexPort as a deployed cohort definition or equate arbitrary-index rejection with the unchecked alias. Parent callsite association remains OPEN.',trust='Approved P6/D188 NativeContractSemanticTransport option A: reclassification, never removal')
(E/'NEB_INDEX_FINAL_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(native_controls=len(checks),composed_credit=0)))
