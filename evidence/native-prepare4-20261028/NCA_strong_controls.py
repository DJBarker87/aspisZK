"""Discriminating controls: nonzero source, known-zero destination/expectation.
All fixed header alternatives are independent branches, each with its own
failing assertion; no serial false assertion hides a later case.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
header='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
attrs='''#[kani::proof]#[kani::unwind(7)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
s=header
for row in [0,1]+list(range(3,14)):
 at=32+5*row if row<=2 else 64+5*row
 s+=f'fn NCA_header_control{row}(){{let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[{at+4}]==1);out[{at+4}]=0;out[{at}..{at+5}].copy_from_slice(&input[{at}..{at+5}]);assert_eq!(out[{at+4}],0,"wrong unchanged byte for row{row}");}}\n'
s+=attrs+'fn NCA_headers_strong_controls(){let row:usize=kani::any();kani::assume(row<13);match row{'+','.join(str(i)+'=>NCA_header_control'+str(row)+'()' for i,row in enumerate([0,1]+list(range(3,14))))+',_=>unreachable!()}}\n'
Path('/private/tmp/NCA_header_controls.rs').write_text(s)
# Row2 control retains the complete original row body and its35 bound.
s=Path('/private/tmp/NCA_K007_row2.rs').read_text()
start=s.index('fn NCA_semantic_ordinary_row2_wrong()')
s=s[:start]+s[start:].replace('let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();','let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[78]==1);out[78]=0;',1).replace('if j>=dst&&j<dst+5+size {assert_ne!(out[j],input[src+j-dst]);}','assert_eq!(out[78],0,"wrong unchanged row2 last payload byte");',1)
s=s.replace('fn NCA_semantic_ordinary_row2_wrong()','fn NCA_row2_strong_control()')
Path('/private/tmp/NCA_row2_control.rs').write_text(s)
# Actual serializer-argument control with a nonzero reached input.
s=Path('/private/tmp/NCA_opening_fixed.rs').read_text().replace('fn NCA_inactive_position()','fn NCA_inactive_strong_control()').replace('assert_eq!(value,NCA_INACTIVE)','assert_eq!(value,E::ZERO,"wrong zero inactive argument")').replace('let inactive:E=unsafe{core::mem::transmute::<[u8;32],E>(kani::any())};','let inactive:E=unsafe{core::mem::transmute::<[u8;32],E>(kani::any())};kani::assume(inactive==E::ONE);')
Path('/private/tmp/NCA_inactive_control.rs').write_text(s)
# Aggregate early errors, excluding the failing finish observer case.
s=Path('/private/tmp/NCA_semantic.rs').read_text().replace('row:0','row:7').replace('assert_eq!(row,0);','assert_eq!(row,7);')
# Use the original aggregate target with a restricted actual branch domain.
s=s.replace('fn NCA_observed_routes()','fn NCA_observed_early_routes()').replace('kani::assume(mode<5);','kani::assume(mode<3);',1)
Path('/private/tmp/NCA_semantic_early.rs').write_text(s)
t=s.replace('fn NCA_observed_early_routes()','fn NCA_observed_early_controls()')
start=t.index('fn NCA_observed_early_controls()');end=t.index('#[kani::proof]',start)
block=t[start:end].replace('assert_eq!(row,7);','assert_eq!(row,0,"wrong zero parse payload");').replace('assert_eq!(NCA_STAGE,2);kani::cover!','assert_eq!(NCA_STAGE,0,"wrong absent public call");kani::cover!').replace('assert_eq!(actual,1);','assert_eq!(actual,0,"wrong zero begin payload");')
t=t[:start]+block+t[end:];Path('/private/tmp/NCA_semantic_early_controls.rs').write_text(t)
# Constructor control: force an observable nonzero source at the selected cell.
s=Path('/private/tmp/NCA_K010_replay.rs').read_text();start=s.index('fn NCA_claim_tail_wrong()')
s=s[:start]+s[start:].replace('kani::assume(i<32&&b<2&&j<22&&a<10);','kani::assume(i<32&&b<2&&j<22&&a<10);kani::assume(sem.roots[b][i]==1&&choice==8);',1).replace('assert_ne!(p.roots[b][i],sem.roots[b][i]);','assert_eq!(p.roots[b][i],0,"wrong zero Prepared root byte");',1)
s=s.replace('fn NCA_claim_tail_wrong()','fn NCA_claim_tail_strong_control()');Path('/private/tmp/NCA_claim_control.rs').write_text(s)
# Both independent opening position controls, preserving identical stubs/35 bound.
s=Path('evidence/native-prepare3-20261028/NBR_K030/sources/NBR_src/crates/aspis-r1-cost-probe/src/NBR_candidate.rs').read_text()
s=header+s[s.index('#[derive(Clone,Copy)]'):]
for n in ['copy_nonoverlapping','copy_from_slice','clone_from_slice','to_vec','realloc']:s=s.replace('NBR_'+n,'KMX_'+n)
s=s.replace('NBR_','NCA_').replace('if mode==1','else if mode==1').replace('if mode==2','else if mode==2')
s=s.replace('fn NCA_opening_positions()','fn NCA_opening_strong_controls()').replace('kani::assume(mode<3&&index<32);','kani::assume(mode>=1&&mode<=2&&index<32);')
s=s.replace('assert_eq!(src.as_ptr() as *const u8,NCA_ROOT);','assert_eq!(src.as_ptr() as *const u8,NCA_ROOT);assert_eq!(*(src.as_ptr() as *const u8).add(NCA_INDEX),0,"wrong zero root byte at append cut");')
s=s.replace('assert_eq!(g[slot],old[slot]);','assert_eq!(g[slot],E::ZERO,"wrong zero unchanged scratch");')
s=s.replace('let old=g;let slot:usize=kani::any();kani::assume(slot<29);','let old=g;let slot:usize=kani::any();kani::assume(slot<29);if mode==1{kani::assume(root[index]==1);}if mode==2{kani::assume(g[slot]==E::ONE);}')
Path('/private/tmp/NCA_opening_controls.rs').write_text(s)
# Preserve source designs as patches only outside individual attempt receipts.
import difflib
for name in ['header_controls','row2_control','inactive_control','semantic_early','semantic_early_controls','claim_control','opening_controls']:
 data=Path('/private/tmp/NCA_'+name+'.rs').read_text()
 (E/('NCA_'+name.upper()+'.patch')).write_text(''.join(difflib.unified_diff([],data.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCA_candidate.rs')))

# Give each alternative a distinct Kani assertion property (assert_eq shares a panic property).
import re
p=Path('/private/tmp/NCA_header_controls.rs');text=p.read_text()
text=re.sub(r'assert_eq!\(out\[(\d+)\],0,"wrong unchanged byte for row(\d+)"\)',r'assert!(out[\1]==0,"wrong unchanged byte for row\2")',text)
text=text.replace('fn NCA_headers_strong_controls()','fn NCA_headers_distinct_controls()')
Path('/private/tmp/NCA_header_controls_distinct.rs').write_text(text)
for file in ['/private/tmp/NCA_opening_controls.rs','/private/tmp/NCA_semantic_early_controls.rs']:
 p=Path(file);text=p.read_text()
 text=text.replace('assert_eq!(*(src.as_ptr() as *const u8).add(NCA_INDEX),0,"wrong zero root byte at append cut")','assert!(*(src.as_ptr() as *const u8).add(NCA_INDEX)==0,"wrong zero root byte at append cut")').replace('assert_eq!(g[slot],E::ZERO,"wrong zero unchanged scratch")','assert!(g[slot]==E::ZERO,"wrong zero unchanged scratch")').replace('assert_eq!(row,0,"wrong zero parse payload")','assert!(row==0,"wrong zero parse payload")').replace('assert_eq!(NCA_STAGE,0,"wrong absent public call")','assert!(NCA_STAGE==0,"wrong absent public call")').replace('assert_eq!(actual,0,"wrong zero begin payload")','assert!(actual==0,"wrong zero begin payload")')
 p.write_text(text)
