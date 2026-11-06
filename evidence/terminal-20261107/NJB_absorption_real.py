from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
observer='''use super::{PreparedQm31Multiplier,M31};
pub fn prepared_words(p:PreparedQm31Multiplier)->[[u32;3];3]{[
 [p.components[0][0].0,p.components[0][1].0,p.components[0][2].0],
 [p.components[1][0].0,p.components[1][1].0,p.components[1][2].0],
 [p.components[2][0].0,p.components[2][1].0,p.components[2][2].0]]}
pub fn prepared_from_words(w:[[u32;3];3])->PreparedQm31Multiplier{PreparedQm31Multiplier{components:[
 [M31(w[0][0]),M31(w[0][1]),M31(w[0][2])],
 [M31(w[1][0]),M31(w[1][1]),M31(w[1][2])],
 [M31(w[2][0]),M31(w[2][1]),M31(w[2][2])]]}}
''';(E/'NJB_observe.rs.txt').write_text(observer)
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p]).decode();a=src.index('fn absorption_lanes_factored(');o=src.index('{',a);f=src.index('core::array::from_fn(|lane| {',o);pre=src[o+1:f];br=f+len('core::array::from_fn(|lane| ');d=1;i=br+1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
lane=src[br+1:i-1]
def logged(s):
 edits={}
 for m in re.finditer(r'\.(mul|add|sub)\(|PreparedQm31Multiplier::new\(',s):
  j=m.end();d=1
  while d:d+=(s[j]=='(')-(s[j]==')');j+=1
  edits[j-1]=',log'+edits.get(j-1,'')
  if m.group(0).startswith('.'):edits[m.start()+1]='NJB_'+edits.get(m.start()+1,'')
 for k,t in sorted(edits.items(),reverse=True):s=s[:k]+t+s[k:]
 return s.replace('PreparedQm31Multiplier::new','NJB_new')
for body in [pre,lane]:assert logged(body).replace('NJB_new','PreparedQm31Multiplier::new').replace('.NJB_','.').replace(',log','')==body
helper=(E/'NJB_residual.rs.txt').read_text().split('fn NJB_copy_residual')[0]
helper=helper.replace('calls:usize}', 'calls:usize,prepared:[[u32;4];3],cache_reply:[[[u32;3];3];3],cache_seen:[[[u32;3];3];3],called_cache:[[u32;3];3],news_at:[usize;3],news:usize}')
code=helper+'''use aspis_core::field::NJB_observe::{prepared_words,prepared_from_words};
fn NJB_new(value:QM31,l:&mut NJB_Log)->PreparedQm31Multiplier{assert!(l.news<3);assert!(canon(words(value)));let j=l.news;l.prepared[j]=words(value);l.news_at[j]=l.calls;let p=prepared_from_words(l.cache_reply[j]);l.cache_seen[j]=prepared_words(p);l.news+=1;p}
trait NJB_PreparedOps{fn NJB_mul(self,r:QM31,l:&mut NJB_Log)->QM31;}
impl NJB_PreparedOps for PreparedQm31Multiplier{fn NJB_mul(self,r:QM31,l:&mut NJB_Log)->QM31{let j=l.calls;assert!(j<17);assert!(canon(words(r)));l.called_cache=prepared_words(self);l.right[j]=words(r);l.kind[j]=3;l.calls+=1;q(l.reply[j])}}
fn log(r:[[u32;4];17],p:[[[u32;3];3];3])->NJB_Log{NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0,prepared:[[0;4];3],cache_reply:p,cache_seen:[[[0;3];3];3],called_cache:[[0;3];3],news_at:[0;3],news:0}}
'''
code+='fn NJB_abs_scales(low:QM31,fixed:QM31,chunk_two:QM31,chunk_eight:QM31,nodes:QM31,log:&mut NJB_Log)->[PreparedQm31Multiplier;3]{'+logged(pre)+'scales}\n'
code+='fn NJB_abs_lane(scales:[PreparedQm31Multiplier;3],openings:&[QM31;16],lane:usize,log:&mut NJB_Log)->QM31{'+logged(lane)+'}\n'
code+='''
#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_absorption_scales(){let a:[[u32;4];5]=kani::any();let r:[[u32;4];17]=kani::any();let caches:[[[u32;3];3];3]=kani::any();for w in a{kani::assume(canon(w));}for w in r{kani::assume(canon(w));}let mut l=log(r,caches);let out=NJB_abs_scales(q(a[0]),q(a[1]),q(a[2]),q(a[3]),q(a[4]),&mut l);let j:usize=kani::any();let limb:usize=kani::any();let k:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(j<7&&limb<4&&k<3&&row<3&&col<3);let left=[a[0],a[1],a[0],a[1],r[3],r[4],a[0]];let right=[a[1],a[2],r[1],a[2],a[3],a[4],r[5]];let kinds=[0,1,0,1,1,1,0];let at=[1,3,7];let replies=[0,2,6];assert_eq!(l.calls,7);assert_eq!(l.news,3);assert_eq!(l.kind[j],kinds[j]);assert_eq!(l.left[j][limb],left[j][limb]);assert_eq!(l.right[j][limb],right[j][limb]);assert_eq!(l.news_at[k],at[k]);assert_eq!(l.prepared[k][limb],r[replies[k]][limb]);assert_eq!(l.cache_seen[k][row][col],caches[k][row][col]);assert_eq!(prepared_words(out[k])[row][col],caches[k][row][col] ^ if cfg!(NJB_invert){1}else{0});}
#[kani::proof]#[kani::unwind(8)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_absorption_lane(){let opened:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let cache:[[[u32;3];3];3]=kani::any();let scales=[prepared_from_words(cache[0]),prepared_from_words(cache[1]),prepared_from_words(cache[2])];let lane:usize=kani::any();kani::assume(lane<16);let group=if lane<2{0}else if lane<8{1}else{2};let reply:[u32;4]=kani::any();kani::assume(canon(words(opened[lane]))&&canon(reply));let mut r=[[0;4];17];r[0]=reply;let mut l=log(r,[[[0;3];3];3]);let out=NJB_abs_lane(scales,&opened,lane,&mut l);let limb:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(limb<4&&row<3&&col<3);assert_eq!(l.calls,1);assert_eq!(l.news,0);assert_eq!(l.kind[0],3);assert_eq!(l.called_cache[row][col],cache[group][row][col] ^ if cfg!(NJB_invert){1}else{0});assert_eq!(l.right[0][limb],words(opened[lane])[limb]);assert_eq!(words(out)[limb],reply[limb]);}
'''
(E/'NJB_absorption.rs.txt').write_text(code)
(E/'NJB_update_absorption.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());f=json.loads((b/'NJB_FROZEN_FILE_PINS.json').read_text());q='crates/aspis-core/src/field.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==f[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\npub mod NJB_observe { include!("NJB_observe.rs"); }\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
for q,n in [('crates/aspis-core/src/NJB_observe.rs','NJB_observe.rs.txt'),('crates/aspis-statement/src/pool_v1/NJB_absorption.rs','NJB_absorption.rs.txt')]:
 p=s/q
 if q in pins:assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q]
 raw=(b/n).read_bytes();p.write_bytes(raw);pins[q]=hashlib.sha256(raw).hexdigest()
(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('actual nine-word prepared carriers installed; earlier token windows excluded from native credit')
''')
x=dict(attempt='NJB_L057',kind='setup',module='NJB_actual_prepared_carriers',sources=['NJB_update_absorption.py','NJB_observe.rs.txt','NJB_absorption.rs.txt'],command=['python3','NJB_update_absorption.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Preserve ACTUAL Prepared type/36-byte carrier; add cfg-only logical-field observation, no production body change')
(E/'NJB_L057.json').write_text(json.dumps(x))
for i,old in [(40,16),(41,17),(42,18),(43,19)]:
 x=json.loads((E/f'NJB_K{old:03}.json').read_text());a=f'NJB_K{i:03}';x['attempt']=a;x['command'][-1]=a+'.json';x['sources']+=['NJB_observe.rs.txt'];x['collect']=[v.replace(f'NJB_K{old:03}',a)for v in x['collect']];x['expected_time']='Actual full prepared-cache carrier replacement, original harness name/property strengthened to all nine words; no field products';(E/(a+'.json')).write_text(json.dumps(x))
print('absorption windows preserve actual nine-word carriers; old token passes explicitly superseded')
