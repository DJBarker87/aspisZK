"""Re-establish quarantined fragments with the exact supplied KMX bodies.
The source snippets are imported, not promoted to whole-carrier closure.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
old=Path('evidence/native-prepare3-20261028')
header='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
attrs='''#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
'''
rel='sources/NBR_src/crates/aspis-r1-cost-probe/src/NBR_candidate.rs'
s=(old/'NBR_K007'/rel).read_text().replace('use super::*;',header)
s=s.replace('#[kani::proof]',attrs+'#[kani::proof]').replace('NBR_','NCA_').replace('#[kani::unwind(2)]','#[kani::unwind(35)]')
# The local134 carrier is intentionally retained and labelled; it is NOT statement6.
wrong=s[s.index(attrs+'#[kani::proof] #[kani::unwind(35)]\nfn NCA_semantic_ordinary_prefix'):]
wrong=wrong.replace('fn NCA_semantic_ordinary_prefix()', 'fn NCA_semantic_ordinary_wrong()').replace('assert_eq!(out[j],if j>=dst&&j<dst+5+size{input[src+j-dst]}else{old});','if j>=dst&&j<dst+5+size {assert_ne!(out[j],input[src+j-dst]);}')
s+='\n'+wrong
# Split the old mitigated whole-row timeout by the actual row2/empty-payload cases.
for suffix,condition in [('empty','row!=2'),('row2','row==2')]:
 t=s.replace('fn NCA_semantic_ordinary_prefix()', 'fn NCA_semantic_ordinary_'+suffix+'()').replace('fn NCA_semantic_ordinary_wrong()', 'fn NCA_semantic_ordinary_'+suffix+'_wrong()')
 t=t.replace('kani::assume(row<14);','kani::assume(row<14&&'+condition+');')
 t=t.replace('kani::cover!(row==2,','kani::cover!(true,')
 (E/('NCA_K007_'+suffix+'.rs.txt')).write_text(t);Path('/private/tmp/NCA_K007_'+suffix+'.rs').write_text(t)
(E/'NCA_K007_replay.rs.txt').write_text(s);Path('/private/tmp/NCA_K007_replay.rs').write_text(s)
s=(old/'NBR_K010'/rel).read_text().replace('use super::*;',header)
s=s.replace('#[kani::proof]',attrs+'#[kani::proof]').replace('NBR_','NCA_')
wrong=s[s.index(attrs+'#[kani::proof]'):].replace('fn NCA_claim_tail_all_fields()', 'fn NCA_claim_tail_wrong()').replace('assert_eq!(p.roots[b][i],sem.roots[b][i]);','assert_ne!(p.roots[b][i],sem.roots[b][i]);')
s+='\n'+wrong
(E/'NCA_K010_replay.rs.txt').write_text(s);Path('/private/tmp/NCA_K010_replay.rs').write_text(s)

# Fixed empty-payload rows isolate the dynamic-position frame timeout.
base=(E/'NCA_K007_empty.rs.txt').read_text()
for row in [0,1]+list(range(3,14)):
 t=base.replace('let row:u8=kani::any();kani::assume(row<14&&row!=2);','let row:u8='+str(row)+';')
 t=t.replace('fn NCA_semantic_ordinary_empty()', 'fn NCA_ordinary_row'+str(row)+'()').replace('fn NCA_semantic_ordinary_empty_wrong()', 'fn NCA_ordinary_row'+str(row)+'_wrong()')
 (E/('NCA_ordinary_row'+str(row)+'.rs.txt')).write_text(t);Path('/private/tmp/NCA_ordinary_row'+str(row)+'.rs').write_text(t)
