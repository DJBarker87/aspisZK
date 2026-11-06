from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;src=(E/'NJB_copy_frozen.rs.txt').read_text();a=src.index('fn pattern_values_windowed');o=src.index('{',a);i=o+1;d=1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[o+1:i-1]
helper=(E/'NJB_factored.rs.txt').read_text().split('fn NJB_path_head(')[0]
def logged(s):
 edits={}
 for m in re.finditer(r'\.(mul|add|sub)\(',s):
  j=m.end();d=1
  while d:d+=(s[j]=='(')-(s[j]==')');j+=1
  edits[j-1]=',log'+edits.get(j-1,'');edits[m.start()+1]='NJB_'+edits.get(m.start()+1,'')
 for k,t in sorted(edits.items(),reverse=True):s=s[:k]+t+s[k:]
 return s
code=helper
code+='''fn NJB_power_step(powers:&mut[QM31;8],mut power:QM31,lambda:QM31,mut slot:usize,log:&mut NJB_Log)->(QM31,usize){powers[slot]=power;power=power.NJB_mul(lambda,log);slot+=1;(power,slot)}
fn NJB_prepare_slot(prepared:&mut[PreparedQm31Multiplier;8],powers:[QM31;8],slot:usize,log:&mut NJB_Log){prepared[slot]=NJB_new(powers[slot],log);}
fn NJB_window_step(mut value:QM31,prepared:[PreparedQm31Multiplier;8],openings:[QM31;16],start:usize,mut slot:usize,log:&mut NJB_Log)->(QM31,usize){value=value.NJB_add(prepared[slot].NJB_mul(openings[start+slot],log),log);slot+=1;(value,slot)}
'''
assigns=re.findall(r'result\[(\d+)\] = (.*?);',body,re.S);assert len(assigns)==14
code+='fn NJB_tail_slot(result:&mut[QM31;14],openings:[QM31;16],prepared:[PreparedQm31Multiplier;8],windows:[QM31;4],coordinate:usize,log:&mut NJB_Log){match coordinate{'
erasures={}
for index,expr in assigns:
 raw=expr
 for old,new in [('window_0','windows[0]'),('window_1','windows[1]'),('window_2','windows[2]'),('window_8','windows[3]')]:expr=expr.replace(old,new)
 expr=logged(expr);erasures[index]=dict(original=raw,logged=expr);code+=index+'=>{result['+index+']='+expr+';},'
code+='_=>panic!("coordinate"),}}\n'
common='''let r:[[u32;4];32]=kani::any();let mut l=log(r,[[[0;3];3];2]);let limb:usize=kani::any();kani::assume(limb<4);'''
attr='#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
code+=attr+'''fn NJB_pattern_power(){'''+common+'''let mut powers:[QM31;8]=unsafe{core::mem::transmute::<[[u32;4];8],[QM31;8]>(kani::any())};let before=powers;let power=q(kani::any());let lambda=q(kani::any());let slot:usize=kani::any();let k:usize=kani::any();kani::assume(slot<8&&k<8&&canon(words(power))&&canon(words(lambda))&&canon(r[0]));let (next,next_slot)=NJB_power_step(&mut powers,power,lambda,slot,&mut l);assert_eq!(l.calls,1);assert_eq!(l.kind[0],0);assert_eq!(l.inputs[0][limb],words(power)[limb]);assert_eq!(l.right[0][limb],words(lambda)[limb]);assert_eq!(words(next)[limb],r[0][limb]);assert_eq!(next_slot,slot+1);assert_eq!(words(powers[k])[limb],(if k==slot{words(power)[limb]}else{words(before[k])[limb]})^if cfg!(NJB_invert){1}else{0});}\n'''
code+=attr+'''fn NJB_pattern_prepare(){'''+common+'''let mut prepared:[PreparedQm31Multiplier;8]=unsafe{core::mem::transmute::<[[[u32;3];3];8],[PreparedQm31Multiplier;8]>(kani::any())};let before=prepared;let powers:[QM31;8]=unsafe{core::mem::transmute::<[[u32;4];8],[QM31;8]>(kani::any())};let cache:[[u32;3];3]=kani::any();l.cache[0]=cache;let slot:usize=kani::any();let k:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(slot<8&&k<8&&row<3&&col<3&&canon(words(powers[slot])));NJB_prepare_slot(&mut prepared,powers,slot,&mut l);assert_eq!(l.calls,1);assert_eq!(l.news,1);assert_eq!(l.kind[0],3);assert_eq!(l.inputs[0][limb],words(powers[slot])[limb]);assert_eq!(prepared_words(prepared[k])[row][col],(if k==slot{cache[row][col]}else{prepared_words(before[k])[row][col]})^if cfg!(NJB_invert){1}else{0});}\n'''
code+=attr+'''fn NJB_pattern_window(){'''+common+'''let prepared:[PreparedQm31Multiplier;8]=unsafe{core::mem::transmute::<[[[u32;3];3];8],[PreparedQm31Multiplier;8]>(kani::any())};let opened:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let value=q(kani::any());let start:usize=kani::any();let slot:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume((start==0||start==1||start==2||start==8)&&slot<8&&row<3&&col<3&&canon(words(value))&&canon(words(opened[start+slot]))&&canon(r[0])&&canon(r[1]));let(out,next)=NJB_window_step(value,prepared,opened,start,slot,&mut l);assert_eq!(l.calls,2);assert_eq!(l.kind[0],4);assert_eq!(l.cache_seen[0][row][col],prepared_words(prepared[slot])[row][col]);assert_eq!(l.right[0][limb],words(opened[start+slot])[limb]);assert_eq!(l.kind[1],1);assert_eq!(l.inputs[1][limb],words(value)[limb]);assert_eq!(l.right[1][limb],r[0][limb]);assert_eq!(next,slot+1);assert_eq!(words(out)[limb],r[1][limb]^if cfg!(NJB_invert){1}else{0});}\n'''
# Expected source-ordered local call logs for each of the14 source assignments.
W=lambda i:f'words(windows[{i}])';O=lambda i:f'words(openings[{i}])';R=lambda i:f'r[{i}]';Z='[0;4]'
specs=[([(4,Z,W(3),7),(1,W(0),R(0),0)],R(1)),([],W(0)),([(4,Z,O(8),6),(2,W(2),R(0),0),(4,Z,O(9),7),(2,R(1),R(2),0)],R(3)),([(4,Z,O(6),6),(2,W(0),R(0),0),(4,Z,O(7),7),(2,R(1),R(2),0)],R(3)),([(4,Z,O(0),0),(4,Z,O(1),1),(1,R(0),R(1),0)],R(2)),([(4,Z,O(6),0),(4,Z,O(7),1),(1,R(0),R(1),0)],R(2))]
for lane in [0,10,1,2]:specs.append(([(4,Z,O(lane),0)],R(0)))
specs += [([(4,Z,'[1051521018,0,0,0]',7),(1,W(3),R(0),0)],R(1)),([],W(2)),([],W(1)),([],W(3))]
code+=attr+'fn NJB_pattern_tail(){'+common+'''let prepared:[PreparedQm31Multiplier;8]=unsafe{core::mem::transmute::<[[[u32;3];3];8],[PreparedQm31Multiplier;8]>(kani::any())};let openings:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let windows:[QM31;4]=unsafe{core::mem::transmute::<[[u32;4];4],[QM31;4]>(kani::any())};let mut out:[QM31;14]=unsafe{core::mem::transmute::<[[u32;4];14],[QM31;14]>(kani::any())};let before=out;for j in 0..16{kani::assume(canon(words(openings[j])));}for j in 0..4{kani::assume(canon(words(windows[j]))&&canon(r[j]));}let coordinate='''
for j in range(14):code+=('if'if j==0 else'else if')+f' cfg!(NJB_tail_{j}){{{j}}}'
code+='else{panic!("select coordinate")};let k:usize=kani::any();let call:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(k<14&&row<3&&col<3);NJB_tail_slot(&mut out,openings,prepared,windows,coordinate,&mut l);match coordinate{'
for j,(events,out) in enumerate(specs):
 kinds=[e[0]for e in events]+[0]*(4-len(events));left=[e[1]for e in events]+[Z]*(4-len(events));right=[e[2]for e in events]+[Z]*(4-len(events));cacheidx=[e[3]for e in events]+[0]*(4-len(events));code+=f'{j}=>{{assert_eq!(l.calls,{len(events)});'
 if events:
  code+='kani::assume(call<'+str(len(events))+');let kinds='+str(kinds)+';let lefts=['+','.join(left)+'];let rights=['+','.join(right)+'];let caches='+str(cacheidx)+';assert_eq!(l.kind[call],kinds[call]);if kinds[call]==4{assert_eq!(l.cache_seen[call][row][col],prepared_words(prepared[caches[call]])[row][col]);}else{assert_eq!(l.inputs[call][limb],lefts[call][limb]);}assert_eq!(l.right[call][limb],rights[call][limb]);'
 code+='assert_eq!(words(out[k])[limb],(if k==coordinate{'+out+'[limb]}else{words(before[k])[limb]})^if cfg!(NJB_invert){1}else{0});},'
code+='_=>panic!("coordinate"),}}\n'
(E/'NJB_windowed.rs.txt').write_text(code);(E/'NJB_WINDOWED_ERASURE.json').write_text(json.dumps(dict(frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),assignments=erasures,source_body=body,map_slot='callback/one-slot prototype; complete Std array::map association remains OPEN'),indent=1))
(E/'NJB_install_windowed_gate.py').write_text('''from pathlib import Path
import json,hashlib,subprocess,sys
b=Path.cwd();s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_windowed.rs"]\\nmod NJB_windowed_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_windowed.rs';(s/q).write_bytes((b/'NJB_windowed.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('windowed powers/callback/window/tail local-record windows installed; validation unchanged',flush=True);sys.exit(subprocess.run([sys.executable,'NJB_gate.py',sys.argv[1]]).returncode)
''')
harnesses=['NJB_pattern_power','NJB_pattern_prepare','NJB_pattern_window']+['NJB_pattern_tail']*14
for j,h in enumerate(harnesses):
 for inv in range(2):
  old='NJB_K097'if inv else'NJB_K096';a=f'NJB_K{98+2*j+inv:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['module']=h;x['command']=['python3','NJB_gate.py',a+'.json'];x['collect']=[p.replace(old,a)for p in x['collect']if p!='NJB_SOURCE_PINS.json'];x['sources']=[p for p in x['sources']if p!='NJB_repair_factored_gate.py']+['NJB_windowed.rs.txt','NJB_WINDOWED_ERASURE.json'];x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_copy_terminal::NJB_windowed_native::'+h
  if j>=3:x['env']['RUSTFLAGS']+=' --cfg NJB_tail_'+str(j-3)
  if a=='NJB_K098':x['command']=['python3','NJB_install_windowed_gate.py',a+'.json'];x['sources']+=['NJB_install_windowed_gate.py'];x['collect']+=['NJB_SOURCE_PINS.json']
  x['expected_time']='One source window '+h+(' coordinate '+str(j-3)if j>=3 else'')+'; actual prepared cache and full raw frame';(E/(a+'.json')).write_text(json.dumps(x))
print('windowed powers/callback/window and14 separately partitioned tail assignments staged')
