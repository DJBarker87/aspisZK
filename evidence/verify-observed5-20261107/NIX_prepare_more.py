from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
common='''
 fn same(a:QM31,b:QM31)->bool{a.c0.a.0==b.c0.a.0&&a.c0.b.0==b.c0.b.0&&a.c1.a.0==b.c1.a.0&&a.c1.b.0==b.c1.b.0}
 fn q()->QM31{kani::any()}
'''
s='''
#[cfg(kani)] mod NIX_more {
 use super::*;
'''+common+'''
 struct PairLog{a:QM31,b:QM31,c:QM31,d:QM31,count:u8,frame:u64}
 fn mul(a:QM31,b:QM31,out:QM31,l:&mut PairLog)->QM31{l.a=a;l.b=b;l.count+=1;out}
 fn add(a:QM31,b:QM31,out:QM31,l:&mut PairLog)->QM31{l.c=a;l.d=b;l.count+=1;out}
 fn pattern_step(values:&mut[QM31;4],pattern_selectors:&[QM31;26],patterns:&[QM31;14],group:usize,mut coordinate:usize,product:QM31,out:QM31,l:&mut PairLog)->usize{
  let pattern=usize::from(COPY_PATTERN_COORDINATE_PATTERNS[coordinate]);
  values[group]=add(values[group],mul(patterns[pattern],pattern_selectors[coordinate],product,l),out,l);
  coordinate+=1;coordinate
 }
 fn pattern_check(negative:bool){
  let mut values:[QM31;4]=kani::any();let selectors:[QM31;26]=kani::any();let patterns:[QM31;14]=kani::any();let group:usize=kani::any();kani::assume(group<4);let coordinate:usize=kani::any();kani::assume(coordinate>=COPY_PATTERN_GROUP_OFFSETS[group]&&coordinate<COPY_PATTERN_GROUP_OFFSETS[group+1]);let i:usize=kani::any();kani::assume(i<4);let before=values[i];let selected=values[group];let product=q();let out=q();let count:u8=kani::any();kani::assume(count<254);let frame:u64=kani::any();let mut l=PairLog{a:q(),b:q(),c:q(),d:q(),count,frame};
  let next=pattern_step(&mut values,&selectors,&patterns,group,coordinate,product,out,&mut l);if negative{l.frame^=1;}
  let pat=usize::from(COPY_PATTERN_COORDINATE_PATTERNS[coordinate]);assert!(pat<14);assert_eq!(next,coordinate+1);assert!(same(l.a,patterns[pat])&&same(l.b,selectors[coordinate])&&same(l.c,selected)&&same(l.d,product));assert_eq!(l.count,count+2);assert_eq!(l.frame,frame);assert!(same(values[i],if i==group{out}else{before}));
 }
 fn pattern_init(negative:bool){let mut values:[QM31;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);let before=values[i];let group=0usize;let coordinate=COPY_PATTERN_GROUP_OFFSETS[group];if negative{values[i].c0.a.0^=1;}assert_eq!(group,0);assert_eq!(coordinate,0);assert!(same(values[i],before));}
 fn pattern_outer(negative:bool){let values:[QM31;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);let before=values[i];let mut group:usize=kani::any();kani::assume(group<4);let old=group;let coordinate=COPY_PATTERN_GROUP_OFFSETS[group+1];group+=1;if negative{group=old;}assert_eq!(group,old+1);assert!(group<=4);assert!(coordinate<=26);assert!(same(values[i],before));}
 fn active_init(negative:bool){let mut sums=[QM31::ZERO;7];let sum=QM31::ZERO;let block=0usize;let coordinate=0usize;if negative{sums[0].c0.a.0=1;}let i:usize=kani::any();kani::assume(i<7);assert!(same(sums[i],QM31::ZERO));assert!(same(sum,QM31::ZERO));assert_eq!(block,0);assert_eq!(coordinate,0);}
 fn active_exit(negative:bool){let sum=q();let mut out=sum;if negative{out.c0.a.0^=1;}assert!(same(out,sum));}
 fn tag_geometry(negative:bool){let c:usize=kani::any();kani::assume(c<30);let mut start=usize::from(COPY_TAG_COORDINATE_OFFSETS[c]);let end=usize::from(COPY_TAG_COORDINATE_OFFSETS[c+1]);if negative{start=273;}assert!(start<=end&&end<=272);assert_eq!(COPY_TAG_COORDINATE_OFFSETS[0],0);assert_eq!(COPY_TAG_COORDINATE_OFFSETS[30],272);}
 fn tag_terms(negative:bool){let i:usize=kani::any();kani::assume(i<272);let mut block=COPY_TAG_TERMS.0[i];let tag=COPY_TAG_TERMS.1[i];if negative{block=64;}assert!(block<64);assert!(tag<aspis_core::field::P);}
 const B:u64=2147483646u64*2147483646u64;
 fn raw_step(raw:&mut[u64;4],products:[u64;4],mut index:usize)->usize{raw[0]+=products[0];raw[1]+=products[1];raw[2]+=products[2];raw[3]+=products[3];index+=1;index}
 fn raw_check(negative:bool){let mut raw:[u64;4]=kani::any();let products:[u64;4]=kani::any();let n:u64=kani::any();kani::assume(n<4);for v in raw{kani::assume(v<=n*B);}for p in products{kani::assume(p<=B);}let index:usize=kani::any();kani::assume(index<272);let i:usize=kani::any();kani::assume(i<4);let old=raw[i];let next=raw_step(&mut raw,products,index);if negative{raw[i]+=1;}assert_eq!(next,index+1);assert_eq!(raw[i],old+products[i]);assert!(raw[i]<=(n+1)*B);}
 struct RedLog{raw:u64,a:M31,b:M31,count:u8,frame:u64}
 fn reduce(x:u64,value:M31,l:&mut RedLog)->M31{l.raw=x;l.count+=1;value}
 fn madd(a:M31,b:M31,value:M31,l:&mut RedLog)->M31{l.a=a;l.b=b;l.count+=1;value}
 fn reduce_step(output:&mut[M31;4],raw:&[u64;4],mut limb:usize,reduced:M31,reply:M31,l:&mut RedLog)->usize{output[limb]=madd(output[limb],reduce(raw[limb],reduced,l),reply,l);limb+=1;limb}
 fn reduce_check(negative:bool){let mut output:[M31;4]=kani::any();let raw:[u64;4]=kani::any();let limb:usize=kani::any();kani::assume(limb<4);let i:usize=kani::any();kani::assume(i<4);let old=output[i];let selected=output[limb];let reduced:M31=kani::any();let reply:M31=kani::any();kani::assume(selected.0<aspis_core::field::P&&reduced.0<aspis_core::field::P&&reply.0<aspis_core::field::P);let count:u8=kani::any();kani::assume(count<254);let frame:u64=kani::any();let mut l=RedLog{raw:kani::any(),a:kani::any(),b:kani::any(),count,frame};let next=reduce_step(&mut output,&raw,limb,reduced,reply,&mut l);if negative{l.frame^=1;}assert_eq!(l.raw,raw[limb]);assert_eq!(l.a.0,selected.0);assert_eq!(l.b.0,reduced.0);assert_eq!(l.count,count+2);assert_eq!(l.frame,frame);assert_eq!(next,limb+1);assert_eq!(output[i].0,if i==limb{reply.0}else{old.0});}
 struct LowLog{args:[QM31;18],kinds:[u8;9],calls:usize,frame:u64}
 fn op(a:QM31,b:QM31,kind:u8,o:&[QM31;9],l:&mut LowLog)->QM31{let i=l.calls;l.args[2*i]=a;l.args[2*i+1]=b;l.kinds[i]=kind;l.calls+=1;o[i]}
 fn low_step(low:&[QM31;16],high:&[QM31;7],sum:QM31,mut coordinate:usize,o:&[QM31;9],l:&mut LowLog)->(usize,QM31){
  let low_sum=match coordinate{
  LOWCASES
  _=>unreachable!("coordinate outside frozen active-mask basis")};
  let sum=op(sum,op(high[coordinate],low_sum,1,o,l),0,o,l);coordinate+=1;(coordinate,sum)
 }
 fn low_check(negative:bool){let low:[QM31;16]=kani::any();let high:[QM31;7]=kani::any();let sum=q();let c:usize=kani::any();kani::assume(c<7);let o:[QM31;9]=kani::any();let seed=q();let frame:u64=kani::any();let mut l=LowLog{args:[seed;18],kinds:[0;9],calls:0,frame};let (next,out)=low_step(&low,&high,sum,c,&o,&mut l);if negative{l.frame^=1;}let mut expected=[(seed,seed);9];let mut n=0usize;
  match c {EXPECTED _=>unreachable!()}
  let i:usize=kani::any();kani::assume(i<18);assert_eq!(next,c+1);assert_eq!(l.calls,n);assert_eq!(l.frame,frame);if i<2*n{assert!(same(l.args[i],if i%2==0{expected[i/2].0}else{expected[i/2].1}));let j=i/2;assert_eq!(l.kinds[j],if j==n-2{1}else{0});}else{assert!(same(l.args[i],seed));}assert!(same(out,o[n-1]));}
'''
seqs=[[11,12],[0,11,12],[0,12],[11],[0,11],[1,2,5,6,9,10,13,14],[0,2,4,6,7,9,10]];cases=[];expected=[]
for c,seq in enumerate(seqs):
 expr=f'low[{seq[0]}]'
 for j,k in enumerate(seq[1:]):expr=f'op({expr},low[{k}],0,o,l)'
 cases.append(f'{c}=>{expr},')
 parts=[]
 for j,k in enumerate(seq[1:]):parts.append(f'expected[{j}]=('+(f'low[{seq[0]}]' if j==0 else f'o[{j-1}]')+f',low[{k}]);')
 j=len(seq)-1;parts.append(f'expected[{j}]=(high[{c}],'+(f'low[{seq[0]}]' if j==0 else f'o[{j-1}]')+f');expected[{j+1}]=(sum,o[{j}]);n={j+2};');expected.append(str(c)+'=>{'+''.join(parts)+'},')
s=s.replace('LOWCASES','\n'.join(cases)).replace('EXPECTED',''.join(expected))
functs=[('pattern', 'pattern_check'),('pattern_init','pattern_init'),('pattern_outer','pattern_outer'),('active_init','active_init'),('active_exit','active_exit'),('tag_geometry','tag_geometry'),('tag_terms','tag_terms'),('raw','raw_check'),('reduce','reduce_check'),('low','low_check')]
for name,fn in functs:
 for neg in [False,True]:s+=f' #[kani::proof] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn {name}_{"control" if neg else "native"}(){{{fn}({str(neg).lower()});}}\n'
s+='}\n';(E/'NIX_more_copy.rs.txt').write_text(s)
s2='''
#[cfg(kani)] mod NIX_more {
 use super::*;
'''+common+'''
 struct Log{lanes:[QM31;4],a:QM31,b:QM31,c:QM31,d:QM31,times:[u8;3],count:u8,frame:u64}
 fn pack(lanes:&[QM31;4],out:QM31,l:&mut Log)->QM31{l.lanes=*lanes;l.times[0]=l.count;l.count+=1;out}
 fn mul(a:QM31,b:QM31,out:QM31,l:&mut Log)->QM31{l.a=a;l.b=b;l.times[1]=l.count;l.count+=1;out}
 fn add(a:QM31,b:QM31,out:QM31,l:&mut Log)->QM31{l.c=a;l.d=b;l.times[2]=l.count;l.count+=1;out}
 fn step(packed:&mut[QM31;24],values:&[QM31;33],selector:QM31,group:usize,packreply:QM31,product:QM31,reply:QM31,l:&mut Log){let start=49;let lanes:[QM31;4]=core::array::from_fn(|slot|{let source=4*group+slot;if source>=start&&source<start+33{values[source-start]}else{QM31::ZERO}});packed[group]=add(packed[group],mul(selector,pack(&lanes,packreply,l),product,l),reply,l);}
 fn check(negative:bool){let mut packed:[QM31;24]=kani::any();let values:[QM31;33]=kani::any();let selector=q();let group:usize=kani::any();kani::assume(group>=12&&group<=20);let i:usize=kani::any();kani::assume(i<24);let slot:usize=kani::any();kani::assume(slot<4);let old=packed[i];let selected=packed[group];let packreply=q();let product=q();let reply=q();let count:u8=kani::any();kani::assume(count<253);let frame:u64=kani::any();let mut l=Log{lanes:kani::any(),a:q(),b:q(),c:q(),d:q(),times:kani::any(),count,frame};step(&mut packed,&values,selector,group,packreply,product,reply,&mut l);if negative{l.frame^=1;}let source=4*group+slot;assert!(same(l.lanes[slot],if source>=49&&source<82{values[source-49]}else{QM31::ZERO}));assert!(same(l.a,selector)&&same(l.b,packreply)&&same(l.c,selected)&&same(l.d,product));assert_eq!(l.times[0],count);assert_eq!(l.times[1],count+1);assert_eq!(l.times[2],count+2);assert_eq!(l.count,count+3);assert_eq!(l.frame,frame);assert!(same(packed[i],if i==group{reply}else{old}));}
 fn init(negative:bool){let first=49usize/4;let mut last=(49usize+33-1)/4;if negative{last+=1;}assert_eq!(first,12);assert_eq!(last,20);}
 fn outer(negative:bool){let start:usize=kani::any();kani::assume(start>=12&&start<=20);let mut range=start..=20;let mut got=range.next();if negative{got=None;}assert_eq!(got,Some(start));assert_eq!(range.is_empty(),start==20);let (lo,hi)=range.into_inner();assert_eq!(lo,if start<20{start+1}else{20});assert_eq!(hi,20);}
'''
for name,fn in [('shared','check'),('shared_init','init'),('shared_outer','outer')]:
 for neg in [False,True]:s2+=f' #[kani::proof] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn {name}_{"control" if neg else "native"}(){{{fn}({str(neg).lower()});}}\n'
s2+='}\n';(E/'NIX_more_semantic.rs.txt').write_text(s2)
# Installation is deferred to a capped support scope, so ongoing jobs retain exact pins.
(E/'NIX_install_more.py').write_text('''from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
for tail,src in [('pair_forest_copy_terminal.rs','NIX_more_copy.rs.txt'),('pair_forest_semantic_terminal.rs','NIX_more_semantic.rs.txt')]:
 n='crates/aspis-statement/src/pool_v1/'+tail;p=B/'NIX_src'/n;s=p.read_text();p.write_text(s+(B/src).read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));print('Independent one-iteration and boundary stages installed; no field multiplication executed; local stages are not composed-row credit')
''')
# semantic file is unchanged in the host; do not copy or replace it in this preparation.
x=json.loads((E/'NIX_L076.json').read_text());x.update(attempt='NIX_L083',module='Independent terminal loop cells and boundaries',sources=['NIX_more_copy.rs.txt','NIX_more_semantic.rs.txt','NIX_install_more.py'],command=['python3','NIX_install_more.py'],collect=['NIX_SOURCE_PINS.json']);(E/'NIX_L083.json').write_text(json.dumps(x,indent=2))
plan=[(77,'copy','pattern'),(79,'copy','pattern_init'),(81,'copy','pattern_outer'),(83,'semantic','shared'),(85,'semantic','shared_init'),(87,'semantic','shared_outer'),(89,'copy','active_init'),(91,'copy','active_exit'),(93,'copy','tag_geometry'),(95,'copy','tag_terms'),(97,'copy','raw'),(99,'copy','reduce'),(68,'copy','low')]
for num,area,fn in plan:
 for neg in [False,True]:
  i=(70 if neg else 68) if num==68 else num+int(neg);a=f'NIX_K{i:03}';p=E/(a+'.json')
  if i in [68,70]:(E/(a+'_UNSUBMITTED.json')).write_text(p.read_text())
  x=json.loads((E/'NIX_K058.json').read_text());mod='pair_forest_copy_terminal'if area=='copy'else'pair_forest_semantic_terminal';hn=f'pool_v1::{mod}::NIX_more::{fn}_{"control" if neg else "native"}';x.update(attempt=a,module=hn);x['command'][2]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]=hn;x['collect']=[a+z for z in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json']];x['expected_time']='Optimized independent '+fn+' one-step/boundary; opaque field replies, no field multiplication, no whole algorithm loop';p.write_text(json.dumps(x,indent=2))
(E/'NIX_MORE_PLAN.json').write_text(json.dumps([dict(positive=f'NIX_K{n:03}',negative=f'NIX_K{70 if n==68 else n+1:03}') for n,_,_ in plan],indent=2))
