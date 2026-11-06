from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();a=src.index('fn add_preweighted_shared_selector<');f=src.index('core::array::from_fn(|slot| {',a);o=f+len('core::array::from_fn(|slot| ');d=1;i=o+1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[o+1:i-1];native=re.sub(r'\bstart\b','49usize',body);native=re.sub(r'\bN\b','33usize',native)
assignment='packed[group] = packed[group].add(selector.mul(qm31_pack_base4(&lanes)));'
assert assignment in src[a:a+1800];trans=assignment.replace('qm31_pack_base4(&lanes)','NJB_pack(&lanes,log)');edits={}
for m in re.finditer(r'\.(mul|add)\(',trans):
 j=m.end();d=1
 while d:d+=(trans[j]=='(')-(trans[j]==')');j+=1
 edits[j-1]=',log'+edits.get(j-1,'');edits[m.start()+1]='NJB_'+edits.get(m.start()+1,'')
for j,t in sorted(edits.items(),reverse=True):trans=trans[:j]+t+trans[j:]
assert trans.replace('.NJB_','.').replace(',log','').replace('NJB_pack(&lanes)','qm31_pack_base4(&lanes)')==assignment
helper=(E/'NJB_residual.rs.txt').read_text().split('fn NJB_copy_residual')[0];helper=helper.replace('calls:usize}','calls:usize,pack_inputs:[[u32;4];4],pack_reply:[u32;4],packs:usize}')
code=helper+'''fn log(r:[[u32;4];17],pack_reply:[u32;4])->NJB_Log{NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0,pack_inputs:[[0;4];4],pack_reply,packs:0}}
fn NJB_pack(lanes:&[QM31;4],l:&mut NJB_Log)->QM31{assert_eq!(l.packs,0);l.pack_inputs=[words(lanes[0]),words(lanes[1]),words(lanes[2]),words(lanes[3])];l.packs+=1;q(l.pack_reply)}
'''
code+='fn NJB_gather(values:&[QM31;33],group:usize,slot:usize)->QM31{'+native+'}\n'
code+='fn NJB_shared_step(packed:&mut[QM31;24],group:usize,selector:QM31,lanes:[QM31;4],log:&mut NJB_Log){'+trans+'}\n'
code+='''
#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_shared_gather(){let values:[QM31;33]=unsafe{core::mem::transmute::<[[u32;4];33],[QM31;33]>(kani::any())};let group:usize=kani::any();let slot:usize=kani::any();let limb:usize=kani::any();kani::assume(group>=12&&group<=20&&slot<4&&limb<4);let out=NJB_gather(&values,group,slot);let source=4*group+slot;let expected=if source>=49&&source<82{words(values[source-49])[limb]}else{0};assert_eq!(words(out)[limb],expected ^ if cfg!(NJB_invert){1}else{0});}
#[kani::proof]#[kani::unwind(27)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_shared_group(){let mut packed:[QM31;24]=unsafe{core::mem::transmute::<[[u32;4];24],[QM31;24]>(kani::any())};let before=packed;let lanes:[QM31;4]=unsafe{core::mem::transmute::<[[u32;4];4],[QM31;4]>(kani::any())};let selector=q(kani::any());let pack_reply:[u32;4]=kani::any();let r0:[u32;4]=kani::any();let r1:[u32;4]=kani::any();let g:usize=kani::any();kani::assume(g>=12&&g<=20);kani::assume(canon(words(before[g]))&&canon(words(selector))&&canon(pack_reply)&&canon(r0)&&canon(r1));let mut r=[[0;4];17];r[0]=r0;r[1]=r1;let mut l=log(r,pack_reply);NJB_shared_step(&mut packed,g,selector,lanes,&mut l);let k:usize=kani::any();let slot:usize=kani::any();let limb:usize=kani::any();kani::assume(k<24&&slot<4&&limb<4);assert_eq!(l.packs,1);assert_eq!(l.calls,2);assert_eq!(l.pack_inputs[slot][limb],words(lanes[slot])[limb]);assert_eq!(l.kind[0],0);assert_eq!(l.kind[1],1);assert_eq!(l.left[0][limb],words(selector)[limb]);assert_eq!(l.right[0][limb],pack_reply[limb]);assert_eq!(l.left[1][limb],words(before[g])[limb]);assert_eq!(l.right[1][limb],r0[limb]);assert_eq!(words(packed[k])[limb],(if k==g{r1[limb]}else{words(before[k])[limb]}) ^ if cfg!(NJB_invert){1}else{0});}
#[kani::proof]#[kani::unwind(12)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_shared_control(){let start=49usize;let n=33usize;let first=start/4;let last=(start+n-1)/4;let mut seen=[0usize;9];let mut calls=0;for group in first..=last{seen[calls]=group;calls+=1;}let i:usize=kani::any();kani::assume(i<9);assert_eq!(calls,9);assert_eq!(seen[i],12+i+if cfg!(NJB_invert){1}else{0});}
'''
(E/'NJB_shared.rs.txt').write_text(code);(E/'NJB_SHARED_ERASURE.json').write_text(json.dumps(dict(source=q,closure_body=body,assignment=assignment,assignment_erasure_equal=True,deployed_instantiation=dict(start=49,N=33,caller='add_value_lanes',source_line=525),source_sha256=hashlib.sha256(src.encode()).hexdigest(),control='data independent 12..=20, body replaced with local recorder only (ad)'),indent=1)+'\n')
(E/'NJB_install_shared.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_shared.rs"]\\nmod NJB_shared_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_shared.rs';(s/q).write_bytes((b/'NJB_shared.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('deployed shared-selector N33/start49 gather/group/control windows installed')
''')
x=dict(attempt='NJB_L067',kind='setup',module='NJB_shared_install',sources=['NJB_install_shared.py','NJB_shared.rs.txt','NJB_SHARED_ERASURE.json'],command=['python3','NJB_install_shared.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Install actual deployed N33/start49 instantiation: arbitrary lane, one group, fixed data-independent control')
(E/'NJB_L067.json').write_text(json.dumps(x))
for i in range(48,54):
 x=json.loads((E/'NJB_K006.json').read_text());a=f'NJB_K{i:03}';which=['gather','group','control'][(i-48)//2];x['attempt']=a;x['module']='NJB_shared_'+which;x['command'][-1]=a+'.json';x['sources']+=['NJB_shared.rs.txt','NJB_SHARED_ERASURE.json'];x['native_command']=[v.replace('pool_v1::pair_forest_copy_terminal::NJB_native::NJB_residual','pool_v1::pair_forest_semantic_terminal::NJB_shared_native::NJB_shared_'+which)for v in x['native_command']];x['collect']=[p.replace('NJB_K006',a)for p in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i%2 else'');x['expected_time']='Optimized shared-selector '+which+' window, field/pack calls opaque; N33/start49 only deployed instance';(E/(a+'.json')).write_text(json.dumps(x))
print('shared-selector N33/start49 native windows and fixed control prepared')
