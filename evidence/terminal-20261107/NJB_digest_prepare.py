from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;src=(E/'NJB_semantic_frozen.rs.txt').read_text()
def body(name):
 a=src.index('fn '+name);o=src.index('{',a);i=o+1;d=1
 while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
 return src[o+1:i-1]
def logged(s):
 edits={}
 for m in re.finditer(r'\.(mul|add|sub)\(|PreparedQm31Multiplier::new\(|qm31_pack_base4\(',s):
  j=m.end();d=1
  while d:d+=(s[j]=='(')-(s[j]==')');j+=1
  edits[j-1]=',log'+edits.get(j-1,'')
  if m.group(0).startswith('.'):edits[m.start()+1]='NJB_'+edits.get(m.start()+1,'')
 for k,t in sorted(edits.items(),reverse=True):s=s[:k]+t+s[k:]
 return s.replace('PreparedQm31Multiplier::new','NJB_new').replace('qm31_pack_base4','NJB_pack')
helpers='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use aspis_core::field::NJB_observe::{prepared_words,prepared_from_words};
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn canon(w:[u32;4])->bool{w[0]<2147483647&&w[1]<2147483647&&w[2]<2147483647&&w[3]<2147483647}
struct NJB_Log{inputs:[[u32;4];32],right:[[u32;4];32],reply:[[u32;4];32],kind:[u8;32],calls:usize,cache:[[u32;3];3],cache_seen:[[[u32;3];3];32],packs:[[[u32;4];4];32],lengths:[usize;32]}
fn log(reply:[[u32;4];32],cache:[[u32;3];3])->NJB_Log{NJB_Log{inputs:[[0;4];32],right:[[0;4];32],reply,kind:[0;32],calls:0,cache,cache_seen:[[[0;3];3];32],packs:[[[0;4];4];32],lengths:[0;32]}}
fn emit(a:QM31,b:QM31,k:u8,l:&mut NJB_Log)->QM31{let i=l.calls;assert!(i<32);assert!(canon(words(a))&&canon(words(b)));l.inputs[i]=words(a);l.right[i]=words(b);l.kind[i]=k;l.calls+=1;q(l.reply[i])}
trait NJB_Ops{fn NJB_mul(self,r:Self,l:&mut NJB_Log)->Self;fn NJB_sub(self,r:Self,l:&mut NJB_Log)->Self;}
impl NJB_Ops for QM31{fn NJB_mul(self,r:Self,l:&mut NJB_Log)->Self{emit(self,r,0,l)}fn NJB_sub(self,r:Self,l:&mut NJB_Log)->Self{emit(self,r,2,l)}}
fn NJB_new(a:QM31,l:&mut NJB_Log)->PreparedQm31Multiplier{let i=l.calls;assert!(i<32);assert!(canon(words(a)));l.inputs[i]=words(a);l.kind[i]=3;l.calls+=1;prepared_from_words(l.cache)}
trait NJB_PreparedOps{fn NJB_mul(self,r:QM31,l:&mut NJB_Log)->QM31;}
impl NJB_PreparedOps for PreparedQm31Multiplier{fn NJB_mul(self,r:QM31,l:&mut NJB_Log)->QM31{let i=l.calls;assert!(i<32);assert!(canon(words(r)));l.cache_seen[i]=prepared_words(self);l.right[i]=words(r);l.kind[i]=4;l.calls+=1;q(l.reply[i])}}
fn NJB_pack(a:&[QM31],l:&mut NJB_Log)->QM31{let i=l.calls;assert!(i<32);assert_eq!(a.len(),4);l.packs[i]=[words(a[0]),words(a[1]),words(a[2]),words(a[3])];l.lengths[i]=a.len();l.kind[i]=5;l.calls+=1;q(l.reply[i])}
'''
code=helpers;erasure={}
for name in ['left_digest_packed_selector_tensor','optional_carry_packed_selector_tensor']:
 b=body(name);loggedbody=logged(b);assert loggedbody.replace('NJB_new','PreparedQm31Multiplier::new').replace('NJB_pack','qm31_pack_base4').replace('.NJB_','.').replace(',log','')==b
 erasure[name]={'frozen_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'body':b,'logged_body':loggedbody}
 args='high:QM31,opened:[QM31;POSEIDON2_WIDTH],expected:Digest'if name.startswith('left')else'carry:usize,opened:[QM31;POSEIDON2_WIDTH],high:QM31,frontier:Digest'
 code+=f'fn NJB_{name}({args},log:&mut NJB_Log)->[QM31;2]{{{loggedbody}}}\n'
common='''let w:[[u32;4];16]=kani::any();let opened:[QM31;16]=unsafe{core::mem::transmute(w)};let expected:[M31;8]=unsafe{core::mem::transmute::<[u32;8],[M31;8]>(kani::any())};let high=q(kani::any());let r:[[u32;4];32]=kani::any();let c:[[u32;3];3]=kani::any();kani::assume(canon(words(high)));for j in 0..8{kani::assume(canon(w[j])&&expected[j].0<2147483647);}for j in 0..32{kani::assume(canon(r[j]));}let mut l=log(r,c);let limb:usize=kani::any();let j:usize=kani::any();let g:usize=kani::any();let slot:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(limb<4&&j<8&&g<2&&slot<4&&row<3&&col<3);'''
checks='''assert_eq!(l.calls,13);assert_eq!(l.kind[0],3);assert_eq!(l.inputs[0][limb],words(high)[limb]);assert_eq!(l.kind[1+j],2);assert_eq!(l.inputs[1+j][limb],w[j][limb]);assert_eq!(l.right[1+j][limb],if limb==0{expected[j].0}else{0});assert_eq!(l.kind[9+2*g],5);assert_eq!(l.lengths[9+2*g],4);assert_eq!(l.packs[9+2*g][slot][limb],r[1+4*g+slot][limb]);assert_eq!(l.kind[10+2*g],4);assert_eq!(l.cache_seen[10+2*g][row][col],c[row][col]);assert_eq!(l.right[10+2*g][limb],r[9+2*g][limb]);assert_eq!(words(out[g])[limb],r[10+2*g][limb]^if cfg!(NJB_invert){1}else{0});'''
for name,call,guard in [('NJB_left_digest','NJB_left_digest_packed_selector_tensor(high,opened,expected,&mut l)',''),('NJB_optional_carry','NJB_optional_carry_packed_selector_tensor(carry,opened,high,expected,&mut l)','let carry:usize=kani::any();')]:
 code+='#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn '+name+'(){'+common+guard+'let out='+call+';'
 if guard:code+='if carry<20{'+checks+'}else{assert_eq!(l.calls,0);assert_eq!(words(out[g])[limb],0^if cfg!(NJB_invert){1}else{0});}'
 else:code+=checks
 code+='}\n'
# Recipient one source loop step, actual Option prologue split from body, never Option<fn>.
b=body('optional_recipient_packed_selector_tensor');a=b.index('let lane = 4 * group;');end=b.index('group += 1;',a)+len('group += 1;');step=b[a:end];erasure['optional_recipient_packed_selector_tensor']={'frozen_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'step':step,'logged_step':logged(step)}
code+='fn NJB_recipient_step(contribution:&mut[QM31;2],mut group:usize,opened:[QM31;16],expected:Digest,prepared_high:PreparedQm31Multiplier,log:&mut NJB_Log)->usize{'+logged(step)+'group}\n'
code+='''#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_recipient_step_proof(){'''+common+'''let mut contribution:[QM31;2]=unsafe{core::mem::transmute::<[[u32;4];2],[QM31;2]>(kani::any())};let before=contribution;let next=NJB_recipient_step(&mut contribution,g,opened,expected,prepared_from_words(c),&mut l);let k:usize=kani::any();kani::assume(k<2);assert_eq!(next,g+1);assert_eq!(l.calls,6);assert_eq!(l.kind[slot],2);assert_eq!(l.inputs[slot][limb],w[4*g+slot][limb]);assert_eq!(l.right[slot][limb],if limb==0{expected[4*g+slot].0}else{0});assert_eq!(l.kind[4],5);assert_eq!(l.packs[4][slot][limb],r[slot][limb]);assert_eq!(l.lengths[4],4);assert_eq!(l.kind[5],4);assert_eq!(l.cache_seen[5][row][col],c[row][col]);assert_eq!(l.right[5][limb],r[4][limb]);assert_eq!(words(contribution[k])[limb],(if k==g{r[5][limb]}else{words(before[k])[limb]})^if cfg!(NJB_invert){1}else{0});}
'''
(E/'NJB_digest.rs.txt').write_text(code);(E/'NJB_DIGEST_ERASURE.json').write_text(json.dumps(erasure,indent=2))
(E/'NJB_install_digest.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_digest.rs"]\\nmod NJB_digest_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_digest.rs';(s/q).write_bytes((b/'NJB_digest.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('real prepared digest/carry/recipient windows installed')
''')
x=json.loads((E/'NJB_L067.json').read_text());x.update(attempt='NJB_L070',module='NJB_digest_install',sources=['NJB_install_digest.py','NJB_digest.rs.txt','NJB_DIGEST_ERASURE.json'],command=['python3','NJB_install_digest.py']);(E/'NJB_L070.json').write_text(json.dumps(x))
for i,harness in enumerate(['NJB_left_digest','NJB_optional_carry','NJB_recipient_step_proof']):
 for inv in range(2):
  old='NJB_K0'+('49'if inv else'48');a=f'NJB_K{54+2*i+inv:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['module']=harness;x['command'][-1]=a+'.json';x['sources']+=['NJB_digest.rs.txt','NJB_DIGEST_ERASURE.json'];x['collect']=[n.replace(old,a)for n in x['collect']];x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_semantic_terminal::NJB_digest_native::'+harness;(E/(a+'.json')).write_text(json.dumps(x))
print('three actual-carrier native windows staged')
