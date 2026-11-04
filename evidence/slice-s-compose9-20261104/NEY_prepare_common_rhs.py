"""Split common-field RHSs; these do not certify the owned aggregate handoff."""
from NEY_native_patch import E,frozen,program
import sys,json,subprocess
slot=int(sys.argv[1]);mode=sys.argv[2];assert 0<=slot<4 and mode in ['positive','value']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
f=frozen('programs/r1-cost-probe/src/r1_pool_adapter.rs');a=f.index('fn asq8_common(');z=f.index('\n}',a)+2;original=f[a:z]
field=['master_account','checkpoint_account','selected_lane_account','output_lane'][slot]
expression=['authenticated.master_account','authenticated.checkpoint_account','authenticated.selected_lane_account','authenticated.selected_lane.lane_id'][slot]
assert field+': '+expression+',' in original
if slot<3:
 ty='[u8;32]';setup='let expected:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);';arg='expected';observe='native[j]==expected[j]'
 definition='struct A{'+field+':'+ty+'}\n'
else:
 setup='let expected:u8=kani::any();';arg='Lane{lane_id:expected}';definition='struct Lane{lane_id:u8}\nstruct A{selected_lane:Lane}\n';observe='native==expected'
key=field if slot<3 else 'selected_lane'
body=definition+'#[kani::proof]\nfn common_rhs(){'+setup+'let authenticated=A{'+key+':'+arg+'};let native='+expression+';assert!('+observe+('^1' if mode=='value' else '')+');}\n'
program(body,'NEY_common_rhs')
(E/'NEY_COMMON_RHS_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,frozen_body=original,frozen_expression=expression,source=body,classification='source-isolated exact RHS; projected typed input; SUPPORT ONLY, no whole native asq8_common or allocation/frame association'),indent=1)+'\n')
