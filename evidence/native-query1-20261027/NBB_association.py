"""Frozen row-source partition check; no source or launcher modification."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
native=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
h=(E/'NBB_harness.rs.txt').read_text()
def body(s,name):
 start=s.index('{',s.index('fn '+name+'('));depth=0
 for i in range(start,len(s)):
  if s[i]=='{':depth+=1
  if s[i]=='}':
   depth-=1
   if depth==0:return s[start+1:i]
 raise AssertionError(name)
def compact(s):return re.sub(r'\s+','',s)
r=compact(body(native,'update_residue_row'))
a=compact(body(h,'NBB_add_iteration'))
push=compact(body(native,'push'))
scalar='old+u64::from(limb)*u64::from(basis.0)'
checks={
 'frozen_add_pass': 'forjin0..4{letold=residue_limb_at(row,j);letlimb=power_limb_at(&limbs,j);row[j]='+scalar+';}' in r,
 'factored_add_expression': compact(body(h,'NBB_add'))==scalar,
 'one_add_iteration': a=='letold=residue_limb_at(row,j);letlimb=power_limb_at(limbs,j);row[j]=NBB_add(old,limb,basis);',
 'frozen_fold_pass':'ifflush{forlimbinrow{*limb=(*limb&0x7fff_ffff)+(*limb>>31);}}' in r,
 'factored_fold_expression':compact(body(h,'NBB_fold'))=='(value&0x7fff_ffff)+(value>>31)',
 'frozen_push_borrow_and_call':push=='letflush=self.terms&3==3;update_residue_row(&mutself.raw[index],power,basis,flush);',
 'borrowed_push_continuation':compact(body(h,'NBB_push_selected'))=='letflush=terms&3==3;update_residue_row(row,power,basis,flush);',
 'limb_order':'letlimbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];' in r,
 'native_row_unchanged':body(Path('crates/aspis-r1-cost-probe/src/verifier.rs').read_text(),'update_residue_row')==body(native,'update_residue_row'),
}
assert all(checks.values()),checks
out={'frozen_revision':rev,'frozen_verifier_sha256':hashlib.sha256(native.encode()).hexdigest(),'harness_sha256':hashlib.sha256(h.encode()).hexdigest(),'checks':checks,'method':'one native arbitrary store step plus named emitted integer scalar and four-lane fusion; Vec borrow uses retained std interpretation','callee_theorems':['NBB_Arithmetic.add','NBB_Arithmetic.fold','NBB_RowTrace.native_result','NBB_Push.source','S7OwnedP6RowContract.four_lane_fusion'],'open':'Whole query_values and query_loop native/model association is not established by these row checks.'}
(E/'NBB_ASSOCIATION.json').write_text(json.dumps(out,indent=2)+'\n')
