from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();a=src.index('fn finish_pattern_basis_values(');b=src.index('while coordinate <',a);o=src.index('{',b);d=1;i=o+1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[o+1:i-1];insert={}
for m in re.finditer(r'\.(mul|add)\(',body):
 j=m.end();d=1
 while d:d+=(body[j]=='(')-(body[j]==')');j+=1
 insert[j-1]=',log'+insert.get(j-1,'');insert[m.start()+1]='NJB_'+insert.get(m.start()+1,'')
new=body
for k,t in sorted(insert.items(),reverse=True):new=new[:k]+t+new[k:]
assert new.replace('.NJB_','.').replace(',log','')==body
helper=(E/'NJB_residual.rs.txt').read_text().split('fn NJB_copy_residual')[0]
code=helper+'fn NJB_pattern_step(values:&mut[QM31;4],pattern_selectors:&[QM31;26],patterns:&[QM31;14],group:usize,mut coordinate:usize,log:&mut NJB_Log)->usize{'+new+'coordinate}\n'
code+='''
#[kani::proof]#[kani::unwind(8)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_pattern_inner(){let patterns:[QM31;14]=unsafe{core::mem::transmute::<[[u32;4];14],[QM31;14]>(kani::any())};let selectors:[QM31;26]=unsafe{core::mem::transmute::<[[u32;4];26],[QM31;26]>(kani::any())};let mut values:[QM31;4]=unsafe{core::mem::transmute::<[[u32;4];4],[QM31;4]>(kani::any())};let before=values;let group:usize=kani::any();let coordinate:usize=kani::any();kani::assume(group<4);kani::assume(coordinate>=COPY_PATTERN_GROUP_OFFSETS[group]&&coordinate<COPY_PATTERN_GROUP_OFFSETS[group+1]);let p=usize::from(COPY_PATTERN_COORDINATE_PATTERNS[coordinate]);let r0:[u32;4]=kani::any();let r1:[u32;4]=kani::any();kani::assume(canon(words(patterns[p]))&&canon(words(selectors[coordinate]))&&canon(words(before[group]))&&canon(r0)&&canon(r1));let mut r=[[0;4];17];r[0]=r0;r[1]=r1;let mut log=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0};let next=NJB_pattern_step(&mut values,&selectors,&patterns,group,coordinate,&mut log);let limb:usize=kani::any();let k:usize=kani::any();kani::assume(limb<4&&k<4);assert_eq!(log.calls,2);assert_eq!(log.kind[0],0);assert_eq!(log.kind[1],1);assert_eq!(log.left[0][limb],words(patterns[p])[limb]);assert_eq!(log.right[0][limb],words(selectors[coordinate])[limb]);assert_eq!(log.left[1][limb],words(before[group])[limb]);assert_eq!(log.right[1][limb],r0[limb]);assert_eq!(next,coordinate+1);assert_eq!(words(values[k])[limb],(if k==group{r1[limb]}else{words(before[k])[limb]}) ^ if cfg!(NJB_invert){1}else{0});}
struct NJB_Inner{group:usize,start:usize,end:usize,before:[QM31;4],selectors:[QM31;26],patterns:*const [QM31;14],reply:[QM31;4],calls:usize}
fn NJB_inner(values:&mut[QM31;4],selectors:&[QM31;26],patterns:&[QM31;14],g:usize,start:usize,end:usize,log:&mut NJB_Inner){assert_eq!(log.calls,0);log.group=g;log.start=start;log.end=end;log.before=*values;log.selectors=*selectors;log.patterns=patterns;*values=log.reply;log.calls+=1;}
fn NJB_pattern_outer_step(mut values:[QM31;4],pattern_selectors:[QM31;26],patterns:&[QM31;14],mut group:usize,log:&mut NJB_Inner)->([QM31;4],usize){let coordinate=COPY_PATTERN_GROUP_OFFSETS[group];NJB_inner(&mut values,&pattern_selectors,patterns,group,coordinate,COPY_PATTERN_GROUP_OFFSETS[group+1],log);group+=1;(values,group)}
#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_pattern_outer(){let patterns:[QM31;14]=unsafe{core::mem::transmute::<[[u32;4];14],[QM31;14]>(kani::any())};let selectors:[QM31;26]=unsafe{core::mem::transmute::<[[u32;4];26],[QM31;26]>(kani::any())};let values:[QM31;4]=unsafe{core::mem::transmute::<[[u32;4];4],[QM31;4]>(kani::any())};let reply:[QM31;4]=unsafe{core::mem::transmute::<[[u32;4];4],[QM31;4]>(kani::any())};let g:usize=kani::any();kani::assume(g<4);let mut log=NJB_Inner{group:0,start:0,end:0,before:values,selectors,patterns:core::ptr::null(),reply,calls:0};let(out,next)=NJB_pattern_outer_step(values,selectors,&patterns,g,&mut log);let k:usize=kani::any();let j:usize=kani::any();let limb:usize=kani::any();kani::assume(k<4&&j<26&&limb<4);assert_eq!(log.calls,1);assert_eq!(log.group,g);assert_eq!(log.start,COPY_PATTERN_GROUP_OFFSETS[g]);assert_eq!(log.end,COPY_PATTERN_GROUP_OFFSETS[g+1]);assert_eq!(next,g+1);assert_eq!(words(log.before[k])[limb],words(values[k])[limb]);assert_eq!(words(log.selectors[j])[limb],words(selectors[j])[limb]);assert!(core::ptr::eq(log.patterns,&patterns));assert_eq!(words(out[k])[limb],words(reply[k])[limb] ^ if cfg!(NJB_invert){1}else{0});}
'''
(E/'NJB_pattern.rs.txt').write_text(code);table={}
for n in ['COPY_PATTERN_COORDINATE_PATTERNS','COPY_PATTERN_GROUP_OFFSETS']:
 m=re.search(n+r'[^=]*=\s*\[(.*?)\];',src,re.S);table[n]=[int(v.strip())for v in m.group(1).split(',')if v.strip()]
(E/'NJB_PATTERN_TABLE.json').write_text(json.dumps(dict(source=q,body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),erasure_equal=True,tables=table),indent=1)+'\n')
(E/'NJB_install_pattern.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_pattern.rs"]\\nmod NJB_pattern_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_pattern.rs';(s/q).write_bytes((b/'NJB_pattern.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('pattern inner iteration and outer cut installed')
''')
x=dict(attempt='NJB_L054',kind='setup',module='NJB_pattern_install',sources=['NJB_install_pattern.py','NJB_pattern.rs.txt','NJB_PATTERN_TABLE.json'],command=['python3','NJB_install_pattern.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Install arbitrary-prestate nested-loop windows; no whole-buffer native proof')
(E/'NJB_L054.json').write_text(json.dumps(x))
for i in range(36,40):
 x=json.loads((E/'NJB_K006.json').read_text());a=f'NJB_K{i:03}';which='inner'if i<38 else'outer';x['attempt']=a;x['module']='NJB_pattern_'+which;x['command'][-1]=a+'.json';x['sources']+=['NJB_pattern.rs.txt','NJB_PATTERN_TABLE.json'];x['native_command']=[v.replace('pool_v1::pair_forest_copy_terminal::NJB_native::NJB_residual','pool_v1::pair_forest_copy_terminal::NJB_pattern_native::NJB_pattern_'+which)for v in x['native_command']];x['collect']=[p.replace('NJB_K006',a)for p in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i%2 else'');x['expected_time']='Optimized pattern '+which+' local-record window, field operations opaque';(E/(a+'.json')).write_text(json.dumps(x))
print('pattern-basis two nested-loop windows prepared with frozen tables and inner erasure')
