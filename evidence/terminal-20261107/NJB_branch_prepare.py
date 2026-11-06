from pathlib import Path
import json
E=Path(__file__).resolve().parent
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
struct NJB_Branch{opened:[QM31;16],high:QM31,expected:Digest,reply:[QM31;2],calls:usize}
fn NJB_branch_call(opened:[QM31;16],high:QM31,expected:Digest,l:&mut NJB_Branch)->[QM31;2]{assert_eq!(l.calls,0);l.opened=opened;l.high=high;l.expected=expected;l.calls+=1;l.reply}
fn NJB_carry_branch(carry:usize,opened:[QM31;16],high:QM31,frontier:Digest,l:&mut NJB_Branch)->[QM31;2]{if carry<20{NJB_branch_call(opened,high,frontier,l)}else{[QM31::ZERO;2]}}
fn NJB_recipient_branch(recipient:Option<Digest>,opened:[QM31;16],high:QM31,l:&mut NJB_Branch)->[QM31;2]{match recipient{Some(expected)=>NJB_branch_call(opened,high,expected,l),None=>[QM31::ZERO;2]}}
#[kani::proof]#[kani::unwind(19)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_optional_branch(){let opened:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let high:QM31=unsafe{core::mem::transmute::<[u32;4],QM31>(kani::any())};let expected:Digest=unsafe{core::mem::transmute::<[u32;8],Digest>(kani::any())};let reply:[QM31;2]=unsafe{core::mem::transmute::<[[u32;4];2],[QM31;2]>(kani::any())};let carry:usize=kani::any();let some:bool=kani::any();let entered=if cfg!(NJB_recipient){some}else{carry<20};let recipient=if some{Some(expected)}else{None};let mut l=NJB_Branch{opened:[QM31::ZERO;16],high:QM31::ZERO,expected:[M31::ZERO;8],reply,calls:0};let out=if cfg!(NJB_recipient){NJB_recipient_branch(recipient,opened,high,&mut l)}else{NJB_carry_branch(carry,opened,high,expected,&mut l)};let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let limb:usize=kani::any();kani::assume(i<16&&j<8&&k<2&&limb<4);assert_eq!(l.calls,if entered{1}else{0});if entered{assert_eq!(words(l.opened[i])[limb],words(opened[i])[limb]);assert_eq!(words(l.high)[limb],words(high)[limb]);assert_eq!(l.expected[j].0,expected[j].0);}assert_eq!(words(out[k])[limb],(if entered{words(reply[k])[limb]}else{0})^if cfg!(NJB_invert){1}else{0});}
''';(E/'NJB_branch.rs.txt').write_text(s)
(E/'NJB_install_branch_gate.py').write_text((E/'NJB_install_path_split_gate.py').read_text().replace('NJB_path_split','NJB_branch').replace('K082 timeout split into one left/right residual+prepared source window','carry/recipient branch-only body-call records installed'))
for region in range(2):
 for inv in range(2):
  old='NJB_K133'if inv else'NJB_K132';a=f'NJB_K{136+2*region+inv:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['module']='NJB_optional_branch';x['command']=['python3','NJB_gate.py',a+'.json'];x['sources']=[p for p in x['sources']if p!='NJB_install_path_split_gate.py']+['NJB_branch.rs.txt'];x['collect']=[p.replace(old,a)for p in x['collect']if p!='NJB_SOURCE_PINS.json'];x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_semantic_terminal::NJB_branch_native::NJB_optional_branch'
  if a=='NJB_K136':x['command']=['python3','NJB_install_branch_gate.py',a+'.json'];x['sources']+=['NJB_install_branch_gate.py'];x['collect']+=['NJB_SOURCE_PINS.json']
  if region:x['env']['RUSTFLAGS']+=' --cfg NJB_recipient'
  x['expected_time']='Data-independent source branch only; exact same callback payload and return2 frame; no true-body semantic claim';(E/(a+'.json')).write_text(json.dumps(x))
