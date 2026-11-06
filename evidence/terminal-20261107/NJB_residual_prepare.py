from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();start=raw.index('fn copy_residual(');op=raw.index('{',start);depth=1;i=op+1
while depth:depth+=(raw[i]=='{')-(raw[i]=='}');i+=1
original=raw[start:i];s=original;insert={}
import re
for m in re.finditer(r'\.(mul|add|sub)\(',s):
 a=m.end();d=1;j=a
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 insert[j-1]=',log'+insert.get(j-1,'');insert[m.start()+1]='NJB_'+insert.get(m.start()+1,'')
for i,t in sorted(insert.items(),reverse=True):s=s[:i]+t+s[i:]
s=s.replace('fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31)','fn NJB_copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31, log:&mut NJB_Log)')
# Reviewed source erasure: every inserted suffix/name and only those edits.
erased=s.replace('NJB_copy_residual','copy_residual').replace(', log:&mut NJB_Log','').replace('.NJB_','.').replace(',log','');assert erased==original
helper='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn canon(w:[u32;4])->bool{w[0]<2147483647&&w[1]<2147483647&&w[2]<2147483647&&w[3]<2147483647}
struct NJB_Log{left:[[u32;4];17],right:[[u32;4];17],reply:[[u32;4];17],kind:[u8;17],calls:usize}
trait NJB_Ops{fn NJB_mul(self,r:Self,l:&mut NJB_Log)->Self;fn NJB_add(self,r:Self,l:&mut NJB_Log)->Self;fn NJB_sub(self,r:Self,l:&mut NJB_Log)->Self;}
fn event(a:QM31,b:QM31,kind:u8,l:&mut NJB_Log)->QM31{let j=l.calls;assert!(j<17);assert!(canon(words(a))&&canon(words(b)));l.left[j]=words(a);l.right[j]=words(b);l.kind[j]=kind;l.calls+=1;q(l.reply[j])}
impl NJB_Ops for QM31{
fn NJB_mul(self,r:Self,l:&mut NJB_Log)->Self{event(self,r,0,l)}
fn NJB_add(self,r:Self,l:&mut NJB_Log)->Self{event(self,r,1,l)}
fn NJB_sub(self,r:Self,l:&mut NJB_Log)->Self{event(self,r,2,l)}}
'''
harness='''
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_residual(){
 let a:[[u32;4];10]=kani::any();let r:[[u32;4];17]=kani::any();
 for w in a {kani::assume(canon(w));}for w in r {kani::assume(canon(w));}
 let row=CopyRowExtension{producer_values:[q(a[0]),q(a[1])],consumer_values:[q(a[2]),q(a[3])],producer_weights:[q(a[4]),q(a[5])],consumer_weights:[q(a[6]),q(a[7])]};
 let mut l=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0};
 let out=NJB_copy_residual(row,q(a[8]),q(a[9]),&mut l);
 let left=[a[9],a[9],a[9],a[9],r[0],r[2],a[4],a[5],r[6],a[6],a[7],r[9],a[8],r[12],r[4],r[5],r[14]];
 let right=[a[0],a[1],a[2],a[3],r[1],r[3],r[1],r[0],r[7],r[3],r[2],r[10],r[5],r[11],r[13],r[8],r[15]];
 let kind=[2,2,2,2,0,0,0,0,1,0,0,1,0,1,0,0,2];
 let j:usize=kani::any();let limb:usize=kani::any();kani::assume(j<17&&limb<4);
 assert_eq!(l.calls,17);assert_eq!(words(out)[limb],r[16][limb]);assert_eq!(l.kind[j],kind[j]);assert_eq!(l.left[j][limb],left[j][limb] ^ if cfg!(NJB_invert){1}else{0});assert_eq!(l.right[j][limb],right[j][limb]);
}
'''
(E/'NJB_residual.rs.txt').write_text(helper+s+harness)
(E/'NJB_RESIDUAL_ERASURE.json').write_text(json.dumps(dict(source=q,original=original,original_sha256=hashlib.sha256(original.encode()).hexdigest(),transformed_sha256=hashlib.sha256(s.encode()).hexdigest(),erasure_equal=True,operation_count=17,actual_field_multiplication_in_Kani=False),indent=1)+'\n')
(E/'NJB_install_residual.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q
assert hashlib.sha256(p.read_bytes()).hexdigest()==json.loads((b/'NJB_FROZEN_FILE_PINS.json').read_text())[q]
p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_residual.rs"]\\nmod NJB_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_residual.rs';(s/q).write_bytes((b/'NJB_residual.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('residual local-record cut installed; 17 ordered opaque operations')
''')
x=dict(attempt='NJB_L009',kind='setup',module='NJB_residual_install',sources=['NJB_install_residual.py','NJB_residual.rs.txt','NJB_RESIDUAL_ERASURE.json'],command=['python3','NJB_install_residual.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Install reviewed local-record field-operation cut only')
(E/'NJB_L009.json').write_text(json.dumps(x))
for i in [6,7]:
 x=json.loads((E/'NJB_K005.json').read_text());a=f'NJB_K{i:03}';x['attempt']=a;x['module']='NJB_residual';x['command'][-1]=a+'.json';x['sources']+=['NJB_residual.rs.txt','NJB_RESIDUAL_ERASURE.json'];x['native_command']=[v.replace('pool_v1::pair_forest_terminal::NJB_native::NJB_semantic_public','pool_v1::pair_forest_copy_terminal::NJB_native::NJB_residual')for v in x['native_command']];x['collect']=[p.replace('NJB_K005',a)for p in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i==7 else'');x['expected_time']='Optimized native dataflow on one straight-line arbitrary pre-state, local 17-operation log; no field multiplication';(E/(a+'.json')).write_text(json.dumps(x))
print('residual transformation erases exactly to frozen body; 17 operations, positive/control configured')
