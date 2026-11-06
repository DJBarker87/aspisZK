from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();a=src.index('fn absorption_lanes_factored(');op=src.index('{',a);f=src.index('core::array::from_fn(|lane| {',op);pre=src[op+1:f];br=f+len('core::array::from_fn(|lane| ');d=1;i=br+1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
lane=src[br+1:i-1]
def logged(s):
 insert={}
 for m in re.finditer(r'\.(mul|add|sub)\(|PreparedQm31Multiplier::new\(',s):
  j=m.end();d=1
  while d:d+=(s[j]=='(')-(s[j]==')');j+=1
  insert[j-1]=',log'+insert.get(j-1,'')
  if m.group(0).startswith('.'):insert[m.start()+1]='NJB_'+insert.get(m.start()+1,'')
 for k,t in sorted(insert.items(),reverse=True):s=s[:k]+t+s[k:]
 return s.replace('PreparedQm31Multiplier','NJB_Prepared')
for orig in [pre,lane]:assert logged(orig).replace('.NJB_','.').replace(',log','').replace('NJB_Prepared','PreparedQm31Multiplier')==orig
helper=(E/'NJB_residual.rs.txt').read_text().split('fn NJB_copy_residual')[0]
helper=helper.replace('calls:usize}', 'calls:usize,prepared:[[u32;4];3],news_at:[usize;3],news:usize}')
prepared='''
#[derive(Clone,Copy)] struct NJB_Prepared{scale:QM31}
impl NJB_Prepared{
 fn new(value:QM31,l:&mut NJB_Log)->Self{assert!(l.news<3);assert!(canon(words(value)));l.prepared[l.news]=words(value);l.news_at[l.news]=l.calls;l.news+=1;Self{scale:value}}
 fn NJB_mul(self,r:QM31,l:&mut NJB_Log)->QM31{event(self.scale,r,0,l)}
}
fn log(r:[[u32;4];17])->NJB_Log{NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0,prepared:[[0;4];3],news_at:[0;3],news:0}}
'''
code=helper+prepared+'fn NJB_abs_scales(low:QM31,fixed:QM31,chunk_two:QM31,chunk_eight:QM31,nodes:QM31,log:&mut NJB_Log)->[NJB_Prepared;3]{'+logged(pre)+'scales}\n'+'fn NJB_abs_lane(scales:[NJB_Prepared;3],openings:&[QM31;16],lane:usize,log:&mut NJB_Log)->QM31{'+logged(lane)+'}\n'
code+='''
#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_absorption_scales(){let a:[[u32;4];5]=kani::any();let r:[[u32;4];17]=kani::any();for w in a{kani::assume(canon(w));}for w in r{kani::assume(canon(w));}let mut l=log(r);let out=NJB_abs_scales(q(a[0]),q(a[1]),q(a[2]),q(a[3]),q(a[4]),&mut l);
 let j:usize=kani::any();let limb:usize=kani::any();let k:usize=kani::any();kani::assume(j<7&&limb<4&&k<3);
 let left=[a[0],a[1],a[0],a[1],r[3],r[4],a[0]];let right=[a[1],a[2],r[1],a[2],a[3],a[4],r[5]];let kinds=[0,1,0,1,1,1,0];let at=[1,3,7];let replies=[0,2,6];
 assert_eq!(l.calls,7);assert_eq!(l.news,3);assert_eq!(l.kind[j],kinds[j]);assert_eq!(l.left[j][limb],left[j][limb] ^ if cfg!(NJB_invert){1}else{0});assert_eq!(l.right[j][limb],right[j][limb]);assert_eq!(l.news_at[k],at[k]);assert_eq!(l.prepared[k][limb],r[replies[k]][limb]);assert_eq!(words(out[k].scale)[limb],r[replies[k]][limb]);}
#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_absorption_lane(){let opened:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let scales:[QM31;3]=unsafe{core::mem::transmute::<[[u32;4];3],[QM31;3]>(kani::any())};let lane:usize=kani::any();kani::assume(lane<16);let group=if lane<2{0}else if lane<8{1}else{2};let reply:[u32;4]=kani::any();kani::assume(canon(words(opened[lane]))&&canon(words(scales[group]))&&canon(reply));let mut r=[[0;4];17];r[0]=reply;let mut l=log(r);let out=NJB_abs_lane([NJB_Prepared{scale:scales[0]},NJB_Prepared{scale:scales[1]},NJB_Prepared{scale:scales[2]}],&opened,lane,&mut l);let limb:usize=kani::any();kani::assume(limb<4);
 assert_eq!(l.calls,1);assert_eq!(l.news,0);assert_eq!(l.kind[0],0);assert_eq!(l.left[0][limb],words(scales[group])[limb] ^ if cfg!(NJB_invert){1}else{0});assert_eq!(l.right[0][limb],words(opened[lane])[limb]);assert_eq!(words(out)[limb],reply[limb]);}
'''
(E/'NJB_absorption.rs.txt').write_text(code);(E/'NJB_ABSORPTION_ERASURE.json').write_text(json.dumps(dict(source=q,scales_body=pre,lane_body=lane,erasure_equal=True,scales_sha256=hashlib.sha256(pre.encode()).hexdigest(),lane_sha256=hashlib.sha256(lane.encode()).hexdigest(),one_native_iteration=True),indent=1))
(E/'NJB_install_absorption.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());f=json.loads((b/'NJB_FROZEN_FILE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==f[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_absorption.rs"]\\nmod NJB_absorption_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_absorption.rs';(s/q).write_bytes((b/'NJB_absorption.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('absorption scales and arbitrary lane cuts installed')
''')
x=dict(attempt='NJB_L023',kind='setup',module='NJB_absorption_install',sources=['NJB_install_absorption.py','NJB_absorption.rs.txt','NJB_ABSORPTION_ERASURE.json'],command=['python3','NJB_install_absorption.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Install prologue and single-lane source-erasing cuts')
(E/'NJB_L023.json').write_text(json.dumps(x))
for i in range(16,20):
 x=json.loads((E/'NJB_K006.json').read_text());a=f'NJB_K{i:03}';which='scales'if i<18 else'lane';x['attempt']=a;x['module']='NJB_absorption_'+which;x['command'][-1]=a+'.json';x['sources']+=['NJB_absorption.rs.txt','NJB_ABSORPTION_ERASURE.json'];x['native_command']=[v.replace('pool_v1::pair_forest_copy_terminal::NJB_native::NJB_residual','pool_v1::pair_forest_semantic_terminal::NJB_absorption_native::NJB_absorption_'+which)for v in x['native_command']];x['collect']=[p.replace('NJB_K006',a)for p in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i%2 else'');x['expected_time']='Optimized absorption '+which+' local-record dataflow; all field products opaque, no whole-buffer loop';(E/(a+'.json')).write_text(json.dumps(x))
print('absorption source-erasing prologue and lane windows prepared')
