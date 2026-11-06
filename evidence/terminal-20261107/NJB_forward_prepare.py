from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();a=s.index('fn active(&self)');o=s.index('{',a);d=1;i=o+1
while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
body=s[o+1:i-1];new=body.replace('self.','selectors.').replace('selectors.active_mask_basis()','NJB_child(selectors,log)');assert new.replace('NJB_child(selectors,log)','selectors.active_mask_basis()').replace('selectors.','self.')==body
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
struct NJB_Call{seen:*const Selectors,calls:usize,reply:QM31}
fn NJB_child(s:&Selectors,l:&mut NJB_Call)->QM31{assert_eq!(l.calls,0);l.seen=s as *const Selectors;l.calls+=1;l.reply}
fn NJB_forward(selectors:&Selectors,log:&mut NJB_Call)->QM31{'''+new+'''}
#[kani::proof]#[kani::unwind(3)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_active_forward(){let s:Selectors=unsafe{core::mem::transmute::<[[u32;4];80],Selectors>(kani::any())};let reply=q(kani::any());let mut log=NJB_Call{seen:core::ptr::null(),calls:0,reply};let out=NJB_forward(&s,&mut log);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(log.calls,1);assert!(core::ptr::eq(log.seen,&s));assert_eq!(words(out)[limb],words(reply)[limb] ^ if cfg!(NJB_invert){1}else{0});}
'''
(E/'NJB_forward.rs.txt').write_text(code);(E/'NJB_FORWARD_ERASURE.json').write_text(json.dumps(dict(source=q,body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),erasure_equal=True,scope='deployed active-mask feature arm; inactive literal arm preserved under its original cfg'),indent=1)+'\n')
(E/'NJB_install_forward.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_forward.rs"]\\nmod NJB_forward_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_forward.rs';(s/q).write_bytes((b/'NJB_forward.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('active same-call forwarding cut installed')
''')
x=dict(attempt='NJB_L049',kind='setup',module='NJB_active_forward_install',sources=['NJB_install_forward.py','NJB_forward.rs.txt','NJB_FORWARD_ERASURE.json'],command=['python3','NJB_install_forward.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Install deployed-arm same-call forwarding cut only; no arithmetic')
(E/'NJB_L049.json').write_text(json.dumps(x))
for i in [34,35]:
 x=json.loads((E/'NJB_K006.json').read_text());a=f'NJB_K{i:03}';x['attempt']=a;x['module']='NJB_active_forward';x['command'][-1]=a+'.json';x['sources']+=['NJB_forward.rs.txt','NJB_FORWARD_ERASURE.json'];x['native_command']=[v.replace('pool_v1::pair_forest_copy_terminal::NJB_native::NJB_residual','pool_v1::pair_forest_copy_terminal::NJB_forward_native::NJB_active_forward')for v in x['native_command']];x['collect']=[p.replace('NJB_K006',a)for p in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i==35 else'');x['expected_time']='Optimized same-input/same-reply active forwarding, no field operations';(E/(a+'.json')).write_text(json.dumps(x))
print('active deployed-arm forwarding positive/control prepared; exact body erasure recorded')
