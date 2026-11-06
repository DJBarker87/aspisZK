from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;src=(E/'NJB_semantic_frozen.rs.txt').read_text()
def body(n):
 a=src.index('fn '+n);o=src.index('{',a);i=o+1;d=1
 while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
 return src[o+1:i-1]
def logged(s):
 edits={}
 for m in re.finditer(r'\.(mul|add|sub)\(|PreparedQm31Multiplier::new\(',s):
  j=m.end();d=1
  while d:d+=(s[j]=='(')-(s[j]==')');j+=1
  edits[j-1]=',log'+edits.get(j-1,'')
  if m.group(0).startswith('.'):edits[m.start()+1]='NJB_'+edits.get(m.start()+1,'')
 for k,t in sorted(edits.items(),reverse=True):s=s[:k]+t+s[k:]
 return s.replace('PreparedQm31Multiplier::new','NJB_new')
helper=(E/'NJB_digest.rs.txt').read_text().split('fn NJB_left_digest_packed_selector_tensor')[0]
helper=helper.replace('cache:[[u32;3];3]','cache:[[[u32;3];3];2]').replace('lengths:[usize;32]}','lengths:[usize;32],news:usize}').replace('lengths:[0;32]}}','lengths:[0;32],news:0}}')
helper=helper.replace('prepared_from_words(l.cache)','{let j=l.news;assert!(j<2);l.news+=1;prepared_from_words(l.cache[j])}')
helper=helper.replace('trait NJB_Ops{','trait NJB_Ops{fn NJB_add(self,r:Self,l:&mut NJB_Log)->Self;').replace('impl NJB_Ops for QM31{','impl NJB_Ops for QM31{fn NJB_add(self,r:Self,l:&mut NJB_Log)->Self{emit(self,r,1,l)}')
code=helper;erasure={}
pb=body('path_lanes_factored');pre=pb[:pb.index('let current0')];prelog=logged(pre).replace('openings.z','z');code+='fn NJB_path_head(path_selector:QM31,z:[QM31;16],log:&mut NJB_Log)->(PreparedQm31Multiplier,PreparedQm31Multiplier,[QM31;17]){'+prelog+'(left,right,path)}\n';erasure['path_head']={'source':pre,'logged':prelog}
# All eight literal blocks share this parameterized frame. Record the originals too.
blocks=[]
for j in range(8):
 a=pb.index(f'let current{j}');end=pb.index(f'let current{j+1}',a)if j<7 else pb.index('\n    path\n',a);blocks.append(pb[a:end])
step='''let current = z[k+1];path[1+k]=left.NJB_mul(succ[k].NJB_sub(current,log),log);path[9+k]=right.NJB_mul(succ[RATE+k].NJB_sub(current,log),log);'''
code+='fn NJB_path_pair(path:&mut[QM31;17],z:[QM31;16],succ:[QM31;16],k:usize,left:PreparedQm31Multiplier,right:PreparedQm31Multiplier,log:&mut NJB_Log){'+step+'}\n';erasure['path_pairs']={'literal_blocks':blocks,'parameterized_logged':step,'association':'k=0..7; source contains eight sequential literal blocks, not a native loop'}
ob=body('occupancy_lanes_factored');p=ob.index('let mut occupancy');f=ob.index('for lane in');ctx=ob[:p];head=ob[p:f];a=ob.index('{',f);end=ob.index('\n    }',a);lane=ob[a+1:end];tail=ob[end+len('\n    }'):ob.rindex('\n    occupancy')]
for name,b,args,ret,finish in [('occupancy_context',ctx,'input_occupancy:QM31,output_occupancy:QM31,opened:&[QM31;16]','(QM31,QM31,QM31,PreparedQm31Multiplier)','(one_minus,both,occupied_selector,empty)'),('occupancy_head',head,'occupied:QM31,inverse:QM31,both:QM31,occupied_selector:QM31,empty:PreparedQm31Multiplier,opened:&[QM31;16]','[QM31;12]','occupancy'),('occupancy_lane',lane,'occupancy:&mut[QM31;12],empty:PreparedQm31Multiplier,opened:&[QM31;16],lane:usize','()','()'),('occupancy_tail',tail,'occupancy:&mut[QM31;12],input_occupancy:QM31,output_occupancy:QM31,expected_output:M31,opened:&[QM31;16],one_minus:QM31','()','()')]:
 t=logged(b);assert t.replace('NJB_new','PreparedQm31Multiplier::new').replace('.NJB_','.').replace(',log','')==b
 erasure[name]={'source':b,'logged':t};code+=f'fn NJB_{name}({args},log:&mut NJB_Log)->{ret}{{{t}{finish}}}\n'
common='''let w:[[u32;4];16]=kani::any();let opened:[QM31;16]=unsafe{core::mem::transmute(w)};let a:[[u32;4];4]=kani::any();let r:[[u32;4];32]=kani::any();let cache:[[[u32;3];3];2]=kani::any();let mut l=log(r,cache);let limb:usize=kani::any();let row:usize=kani::any();let col:usize=kani::any();kani::assume(limb<4&&row<3&&col<3);'''
def assumes(exprs):return 'kani::assume('+ '&&'.join(exprs)+');'
def harness(name,extra):
 global code
 code+='#[kani::proof]#[kani::unwind(35)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn '+name+'(){'+common+extra+'}\n'
harness('NJB_path_head_proof',assumes(['canon(w[0])','canon(a[0])']+[f'canon(r[{j}])'for j in range(6)])+'''let(left,right,out)=NJB_path_head(q(a[0]),opened,&mut l);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<17&&k<6);let kind=[0,2,3,3,2,0];let lefts=[a[0],a[0],r[1],r[0],w[0],r[0]];let rights=[w[0],r[0],[0;4],[0;4],[1,0,0,0],r[4]];assert_eq!(l.calls,6);assert_eq!(l.news,2);assert_eq!(l.kind[k],kind[k]);assert_eq!(l.inputs[k][limb],lefts[k][limb]);if k!=2&&k!=3{assert_eq!(l.right[k][limb],rights[k][limb]);}assert_eq!(prepared_words(left)[row][col],cache[0][row][col]);assert_eq!(prepared_words(right)[row][col],cache[1][row][col]);assert_eq!(words(out[j])[limb],(if j==0{r[5][limb]}else{0})^if cfg!(NJB_invert){1}else{0});''')
harness('NJB_path_pair_proof','''let succ:[QM31;16]=unsafe{core::mem::transmute::<[[u32;4];16],[QM31;16]>(kani::any())};let mut path:[QM31;17]=unsafe{core::mem::transmute::<[[u32;4];17],[QM31;17]>(kani::any())};let before=path;let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<17);'''+assumes(['canon(w[k+1])','canon(words(succ[k]))','canon(words(succ[RATE+k]))']+[f'canon(r[{j}])'for j in range(4)])+'''NJB_path_pair(&mut path,opened,succ,k,prepared_from_words(cache[0]),prepared_from_words(cache[1]),&mut l);assert_eq!(l.calls,4);assert_eq!(l.kind[0],2);assert_eq!(l.kind[1],4);assert_eq!(l.kind[2],2);assert_eq!(l.kind[3],4);assert_eq!(l.inputs[0][limb],words(succ[k])[limb]);assert_eq!(l.inputs[2][limb],words(succ[RATE+k])[limb]);assert_eq!(l.right[0][limb],w[k+1][limb]);assert_eq!(l.right[2][limb],w[k+1][limb]);assert_eq!(l.right[1][limb],r[0][limb]);assert_eq!(l.right[3][limb],r[2][limb]);assert_eq!(l.cache_seen[1][row][col],cache[0][row][col]);assert_eq!(l.cache_seen[3][row][col],cache[1][row][col]);assert_eq!(words(path[j])[limb],(if j==1+k{r[1][limb]}else if j==9+k{r[3][limb]}else{words(before[j])[limb]})^if cfg!(NJB_invert){1}else{0});''')
harness('NJB_occupancy_context_proof',assumes(['canon(w[0])','canon(a[0])','canon(a[1])']+[f'canon(r[{j}])'for j in range(4)])+'''let(one,both,selected,empty)=NJB_occupancy_context(q(a[0]),q(a[1]),&opened,&mut l);let j:usize=kani::any();kani::assume(j<5);let kinds=[2,1,0,2,3];let lefts=[[1,0,0,0],a[0],r[1],r[1],r[3]];let rights=[w[0],a[1],w[0],r[2],[0;4]];assert_eq!(l.calls,5);assert_eq!(l.news,1);assert_eq!(l.kind[j],kinds[j]);assert_eq!(l.inputs[j][limb],lefts[j][limb]);if j!=4{assert_eq!(l.right[j][limb],rights[j][limb]);}assert_eq!(words(one)[limb],r[0][limb]);assert_eq!(words(both)[limb],r[1][limb]);assert_eq!(words(selected)[limb],r[2][limb]);assert_eq!(prepared_words(empty)[row][col],cache[0][row][col]^if cfg!(NJB_invert){1}else{0});''')
harness('NJB_occupancy_head_proof',assumes(['canon(w[9])']+[f'canon(a[{j}])'for j in range(4)]+[f'canon(r[{j}])'for j in range(6)])+'''let out=NJB_occupancy_head(q(a[0]),q(a[1]),q(a[2]),q(a[3]),prepared_from_words(cache[0]),&opened,&mut l);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<12&&k<6);let kinds=[2,0,0,2,0,4];let lefts=[a[0],a[3],w[9],r[2],a[2],[0;4]];let rights=[[1,0,0,0],r[0],a[1],a[0],r[3],a[1]];assert_eq!(l.calls,6);assert_eq!(l.kind[k],kinds[k]);if k!=5{assert_eq!(l.inputs[k][limb],lefts[k][limb]);}assert_eq!(l.right[k][limb],rights[k][limb]);assert_eq!(l.cache_seen[5][row][col],cache[0][row][col]);assert_eq!(words(out[j])[limb],(if j==0{r[1][limb]}else if j==1{r[4][limb]}else if j==2{r[5][limb]}else{0})^if cfg!(NJB_invert){1}else{0});''')
harness('NJB_occupancy_lane_proof','''let mut out:[QM31;12]=unsafe{core::mem::transmute::<[[u32;4];12],[QM31;12]>(kani::any())};let before=out;let lane:usize=kani::any();let j:usize=kani::any();kani::assume(lane<8&&j<12&&canon(w[2+lane])&&canon(r[0]));NJB_occupancy_lane(&mut out,prepared_from_words(cache[0]),&opened,lane,&mut l);assert_eq!(l.calls,1);assert_eq!(l.kind[0],4);assert_eq!(l.cache_seen[0][row][col],cache[0][row][col]);assert_eq!(l.right[0][limb],w[2+lane][limb]);assert_eq!(words(out[j])[limb],(if j==3+lane{r[0][limb]}else{words(before[j])[limb]})^if cfg!(NJB_invert){1}else{0});''')
harness('NJB_occupancy_tail_proof','''let mut out:[QM31;12]=unsafe{core::mem::transmute::<[[u32;4];12],[QM31;12]>(kani::any())};let before=out;let expected:u32=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(expected<2147483647&&j<12&&k<5);'''+assumes(['canon(w[0])','canon(w[10])']+[f'canon(a[{j}])'for j in range(3)]+[f'canon(r[{j}])'for j in range(5)])+'''NJB_occupancy_tail(&mut out,q(a[0]),q(a[1]),M31(expected),&opened,q(a[2]),&mut l);let kinds=[0,0,2,0,1];let lefts=[w[10],a[0],w[0],a[1],r[1]];let rights=[a[2],r[0],[expected,0,0,0],r[2],r[3]];assert_eq!(l.calls,5);assert_eq!(l.kind[k],kinds[k]);assert_eq!(l.inputs[k][limb],lefts[k][limb]);assert_eq!(l.right[k][limb],rights[k][limb]);assert_eq!(words(out[j])[limb],(if j==11{r[4][limb]}else{words(before[j])[limb]})^if cfg!(NJB_invert){1}else{0});''')
(E/'NJB_factored.rs.txt').write_text(code);(E/'NJB_FACTORED_ERASURE.json').write_text(json.dumps(erasure,indent=1));
# Split K072 into frozen lookup and one cell's native arithmetic/copy window.
s=(E/'NJB_endpoint.rs.txt').read_text();s+='''
#[kani::proof]#[kani::unwind(3)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_endpoint_lookup(){let i:usize=kani::any();let consumer:bool=kani::any();kani::assume(i<136);let link=constants::COPY_LINKS[i];let (side,e)=if consumer{(2,link.consumer)}else{(0,link.producer)};let group=side+usize::from(e.slot);let row=usize::from(e.row);let local=row&15;let gc=usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);let pc=usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(e.pattern)][local]);assert!(group<4&&row<1024&&gc<30&&pc<43);assert_eq!(30+gc,30+usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local])+if cfg!(NJB_invert){1}else{0});}
#[kani::proof]#[kani::unwind(19)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_endpoint_cell(){let before:[u32;4]=kani::any();let rhs:[u32;4]=kani::any();let reply:[u32;4]=kani::any();kani::assume(canon(before)&&canon(rhs)&&canon(reply));let mut r=[[0;4];17];r[0]=reply;let mut l=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0,weight:0,selected:[0;4],selected_reply:[0;4],selections:0};let out=q(before).NJB_add(q(rhs),&mut l);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(l.calls,1);assert_eq!(l.kind[0],1);assert_eq!(l.left[0][limb],before[limb]);assert_eq!(l.right[0][limb],rhs[limb]);assert_eq!(words(out)[limb],reply[limb]^if cfg!(NJB_invert){1}else{0});}
''';(E/'NJB_endpoint.rs.txt').write_text(s)
(E/'NJB_install_factored.py').write_text('''from pathlib import Path
import json,hashlib
b=Path.cwd();s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_factored.rs"]\\nmod NJB_factored_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
for q,n in [('crates/aspis-statement/src/pool_v1/NJB_factored.rs','NJB_factored.rs.txt'),('crates/aspis-statement/src/pool_v1/NJB_endpoint.rs','NJB_endpoint.rs.txt')]:
 p=s/q
 if q in pins:assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q]
 p.write_bytes((b/n).read_bytes());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('independent path/occupancy and split endpoint windows installed')
''')
x=json.loads((E/'NJB_L087.json').read_text());x.update(attempt='NJB_L100',module='NJB_factored_install',sources=['NJB_install_factored.py','NJB_factored.rs.txt','NJB_FACTORED_ERASURE.json','NJB_endpoint.rs.txt'],command=['python3','NJB_install_factored.py']);(E/'NJB_L100.json').write_text(json.dumps(x))
for i,h in enumerate(['NJB_path_head_proof','NJB_path_pair_proof','NJB_occupancy_context_proof','NJB_occupancy_head_proof','NJB_occupancy_lane_proof','NJB_occupancy_tail_proof','NJB_endpoint_lookup','NJB_endpoint_cell']):
 for inv in range(2):
  old='NJB_K063'if inv else'NJB_K062';a=f'NJB_K{80+2*i+inv:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['command'][-1]=a+'.json';x['collect']=[p.replace(old,a)for p in x['collect']];x['sources']+=['NJB_factored.rs.txt','NJB_FACTORED_ERASURE.json','NJB_endpoint.rs.txt'];x['native_command'][x['native_command'].index('--harness')+1]=('pool_v1::pair_forest_semantic_terminal::NJB_factored_native::'if i<6 else'pool_v1::pair_forest_copy_terminal::NJB_endpoint_native::')+h;x['expected_time']='Independent source-order native window '+h+'; full actual prepared carrier, no product computation';(E/(a+'.json')).write_text(json.dumps(x))
print('six factored windows and two split endpoint windows staged')
