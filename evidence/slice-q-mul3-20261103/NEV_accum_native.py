"""Audit local-record native cut pairs; never close a slice row by itself."""
from pathlib import Path
import json,copy,re,sys
sys.dont_write_bytecode=True
from NEV_composition import own_native
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(Path(p).read_text())
PAIRS=[('NEV_K038','NEV_K039','basis_inner_iteration','NEV_wrong_basis_inner'),
       ('NEV_K034','NEV_K035','basis_outer_scalar','NEV_wrong_basis_outer'),
       ('NEV_K036','NEV_K037','accumulate_tail_context','NEV_wrong_tail_context'),
       ('NEV_K040','NEV_K041','accumulate_row_context','NEV_wrong_row_context')]
def pair(a,b,function,flag):
 target='verifier::NEV_row_step::'+function
 p=own_native(a,0,target);n=own_native(b,1,target)
 assert p['source_hashes']==n['source_hashes'] and p['native_command']==n['native_command']
 pe=copy.deepcopy(p['env']);ne=copy.deepcopy(n['env'])
 assert ne.pop('RUSTFLAGS')==pe.pop('RUSTFLAGS')+' --cfg '+flag and pe==ne
 assert p['copy_patch_sha256']==n['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for suffix in ['-graph-check.json','-tool-check.json']:
  assert obj(E/(a+suffix))==obj(E/(b+suffix))
 for d in [p,n]:
  s=(E/d['attempt']/'sources/NEV_src/crates/aspis-r1-cost-probe/src/NEV_row_step.rs').read_text()
  assert s.count('fn '+function+'()')==1 and 'cfg!('+flag+')' in s
  assert not re.search(r'\bstatic\s+(?:mut\s+)?\w|Option\s*<\s*fn|stub_verified|proof_for_contract',s)
  assert 'struct NEV_BasisProductLog' in s and 'struct NEV_TailLog' in s
  assert d['source_revision'] and d['peak_rss_kib'] and d['wall_seconds']>=0
 assert re.search(r'\*\* 0 of \d+ failed',(E/a/'stdout.log').read_text())
 return dict(positive=a,negative=b,function=function,flag=flag,status='CHECKED_NATIVE_CUT_ONLY')
if __name__=='__main__':
 result=dict(status='CHECKED_NATIVE_CUTS_ONLY',pairs=[pair(*x) for x in PAIRS],
   closed_rows=[],remaining=['Exact cut-to-actual emitted body transport','Caller-established callee domains','Complete Result/state/effect association','Same-configuration KMX controls','NDT composition gate'])
 (E/'NEV_ACCUM_NATIVE_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
