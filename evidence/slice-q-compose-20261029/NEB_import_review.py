#!/usr/bin/env python3
"""Revalidate committed NEA constructor evidence before importing its laws."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;I=E/'NEB_IMPORTED'
sys.path[:0]=[str(E.parent/'native-ledger3-20261029'),str(E.parent/'native-ledger2-20261028')]
import NDT_review
M=json.loads((E/'NEB_IMPORTS.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
for f in M['files']:
 raw=(R/f['path']).read_bytes();assert sha(raw)==f['sha256'];assert raw==subprocess.check_output(['git','show',M['revision']+':'+f['source_path']],cwd=R)
expected_lock=sha(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],cwd=R))
patch=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
checks=[]
for name,exitcode in [('NEA_K003',0),('NEA_K004',1),('NEA_K005',0),('NEA_K006',1)]:
 d=json.loads((I/name/'receipt.json').read_text());g=json.loads((I/(name+'-graph-check.json')).read_text());lock=json.loads((I/(name+'-lock-check.json')).read_text())
 assert d['exit_status']==exitcode and d['swaps']=='0'
 assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert d['copy_patch_sha256']==patch
 assert lock['before']==lock['after']==expected_lock and lock['unchanged']
 assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples'] and g['lock_sha256']==expected_lock
 assert not json.loads((I/(name+'-source-check.json')).read_text())['errors']
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if name in ['NEA_K005','NEA_K006']:NDT_review.check_features(g,'library-helper')
 else:
  # The constructor macro contains no deployed-sensitive gates other than
  # cfg(kani) attributes, as shown in the committed frozen-body patch.
  raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/r0/domain.rs'],cwd=R).decode()
  start=raw.index('pub fn new(index: usize)');left=raw.index('{',start);depth=1;right=left+1
  while depth:
   depth+=(raw[right]=='{')-(raw[right]=='}');right+=1
  body=raw[start:right]
  assert '#[cfg' not in body
 checks.append(dict(attempt=name,exit_status=exitcode,lock_unchanged=True,feature_association='full deployed verifier list' if name[-1] in '56' else 'core r0; constructor body feature invariant'))
d=json.loads((I/'NEA_L005/receipt.json').read_text());assert d['exit_status']==0 and d['swaps']=='0'
assert sha((I/'NEA_Index.lean').read_bytes())==d['source_hashes']['NEA_generated/NEA_Index.lean']
assert len(d['print_axioms'])==5 and all('sorryAx' not in a and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in a for a in d['print_axioms'])
(E/'NEB_NEA_REVIEW.json').write_text(json.dumps(dict(revision=M['revision'],files_verified=len(M['files']),checks=checks,leaf_status='CLOSED-CONDITIONAL successful-index correspondence',composition_status='OPEN; no for_range call-site proof inferred',copy_patch_sha256=patch,print_axioms=d['print_axioms']),indent=1)+'\n')
print(json.dumps(dict(verified=True,files=len(M['files']),native_attempts_replayed=0,lean_attempts_replayed=0,composition_credit=0)))
