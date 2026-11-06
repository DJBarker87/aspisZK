from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NJB_copy_frozen.rs.txt').read_text();a=s.index('fn accumulate_endpoint_selector_tensor_basis(');o=s.index('{',a);i=o+1;d=1
while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
body=s[o+1:i-1];logged=body.replace('selected_binary_weight(high, weight)','NJB_selected_binary_weight(high, weight, log)')
# Add local log to each add/mul_m31 call while retaining cfg arms verbatim.
import re
edits={}
for m in re.finditer(r'\.(add|mul_m31)\(',logged):
 j=m.end();d=1
 while d:d+=(logged[j]=='(')-(logged[j]==')');j+=1
 edits[j-1]=',log'+edits.get(j-1,'');edits[m.start()+1]='NJB_'+edits.get(m.start()+1,'')
for k,t in sorted(edits.items(),reverse=True):logged=logged[:k]+t+logged[k:]
assert logged.replace('.NJB_','.').replace(',log','').replace('NJB_selected_binary_weight(high, weight, log)','selected_binary_weight(high, weight)')==body
helper=(E/'NJB_residual.rs.txt').read_text().split('fn NJB_copy_residual')[0]
helper=helper.replace('calls:usize}', 'calls:usize,weight:u32,selected:[u32;4],selections:usize}')
code=helper+'''fn NJB_selected_binary_weight(high:QM31,weight:M31,l:&mut NJB_Log)->QM31{assert_eq!(l.selections,0);l.selected=words(high);l.weight=weight.0;l.selections+=1;q(l.reply[0])}
fn NJB_endpoint(scratch:&mut[QM31],side:usize,endpoint:CompiledPoolV1PairForestEndpoint,tag:u32,weight:M31,selectors:&Selectors,log:&mut NJB_Log){'''+logged+'''}
#[kani::proof]#[kani::unwind(105)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_endpoint_step(){let selectors:Selectors=unsafe{core::mem::transmute::<[[u32;4];80],Selectors>(kani::any())};let mut scratch:[QM31;103]=unsafe{core::mem::transmute::<[[u32;4];103],[QM31;103]>(kani::any())};let before=scratch;let index:usize=kani::any();let first=if cfg!(NJB_partition_0){0}else if cfg!(NJB_partition_1){34}else if cfg!(NJB_partition_2){68}else if cfg!(NJB_partition_3){102}else{panic!("partition required")};kani::assume(index>=first&&index<first+34);let consumer:bool=kani::any();let link=constants::COPY_LINKS[index];let (side,endpoint)=if consumer{(2,link.consumer)}else{(0,link.producer)};let group=side+usize::from(endpoint.slot);let row=usize::from(endpoint.row);let local=row&15;let gc=usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);let pc=usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]);assert!(group<4&&row<1024&&gc<30&&pc<43);let wi=30+gc;let pi=60+pc;let weight:u32=kani::any();kani::assume(weight<=1);let r0:[u32;4]=kani::any();let r1:[u32;4]=kani::any();let r2:[u32;4]=kani::any();kani::assume(canon(words(selectors.high[row>>4]))&&canon(words(before[wi]))&&canon(words(before[pi]))&&canon(r0)&&canon(r1)&&canon(r2));let mut r=[[0;4];17];r[0]=r0;r[1]=r1;let mut log=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0,weight:0,selected:[0;4],selections:0};
// Selection's reply and the first add's reply have distinct slots.
log.reply[0]=r0;NJB_endpoint(&mut scratch,side,endpoint,link.tag,M31(weight),&selectors,&mut log);let k:usize=kani::any();let limb:usize=kani::any();kani::assume(k<103&&limb<4);assert_eq!(log.selections,1);assert_eq!(log.weight,weight);assert_eq!(log.selected[limb],words(selectors.high[row>>4])[limb]);assert_eq!(log.calls,2);assert_eq!(log.kind[0],1);assert_eq!(log.kind[1],1);assert_eq!(log.left[0][limb],words(before[wi])[limb]);assert_eq!(log.right[0][limb],r0[limb]);assert_eq!(log.left[1][limb],words(before[pi])[limb]);assert_eq!(log.right[1][limb],words(selectors.high[row>>4])[limb]);assert_eq!(words(scratch[k])[limb],(if k==wi{r0[limb]}else if k==pi{r1[limb]}else{words(before[k])[limb]})^if cfg!(NJB_invert){1}else{0});}
'''
# Distinct selection reply is stored outside the field reply array (no forced equality).
code=code.replace('selected:[u32;4],selections:usize','selected:[u32;4],selected_reply:[u32;4],selections:usize').replace('l.selections+=1;q(l.reply[0])','l.selections+=1;q(l.selected_reply)').replace('selected:[0;4],selections:0','selected:[0;4],selected_reply:r2,selections:0').replace('log.right[0][limb],r0[limb]','log.right[0][limb],r2[limb]')
(E/'NJB_endpoint.rs.txt').write_text(code);(E/'NJB_ENDPOINT_ERASURE.json').write_text(json.dumps(dict(frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),body=body,logged_body=logged,partition='four contiguous 34-link intervals cover all136 genuine endpoints, both sides',features='deployed tag-dot: dormant mul_m31 arm not reached',field_replies='selected reply r2; first add r0; second add r1'),indent=1))
(E/'NJB_install_endpoint.py').write_text((E/'NJB_install_tag.py').read_text().replace('NJB_tag','NJB_endpoint').replace('tag lookup/raw-add/reduce windows installed; multiplication logged only','genuine-endpoint four-window native frame installed'))
x=json.loads((E/'NJB_L082.json').read_text());x.update(attempt='NJB_L087',module='NJB_endpoint_install',sources=['NJB_install_endpoint.py','NJB_endpoint.rs.txt','NJB_ENDPOINT_ERASURE.json'],command=['python3','NJB_install_endpoint.py']);(E/'NJB_L087.json').write_text(json.dumps(x))
for region in range(4):
 for inv in range(2):
  old='NJB_K063'if inv else'NJB_K062';a=f'NJB_K{72+2*region+inv:03}';x=json.loads((E/(old+'.json')).read_text());x['attempt']=a;x['command'][-1]=a+'.json';x['collect']=[p.replace(old,a)for p in x['collect']];x['sources']+=['NJB_endpoint.rs.txt','NJB_ENDPOINT_ERASURE.json'];x['env']['RUSTFLAGS']+=' --cfg NJB_partition_'+str(region);x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_copy_terminal::NJB_endpoint_native::NJB_endpoint_step';x['expected_time']='One real frozen endpoint update, arbitrary103-cell frame, binary-weight callee log, partition '+str(region);(E/(a+'.json')).write_text(json.dumps(x))
