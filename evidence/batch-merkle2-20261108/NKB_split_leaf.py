from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;raw=Path('crates/aspis-r1-cost-probe/src/candidate.rs').read_text();a=raw.index('        let key = batch_key_at(&keys, key_position);');m=raw.index('        if d > 0 && same_batch_index',a);b=raw.index('\n    }\n    let count',m);prefix=raw[a:m];dedup=raw[m:b]
p=E/'NKB_fragments.rs';s=p.read_text();s+='\nfn prefix_fragment<H:Digest32>(proof:&[u8],tree:usize,hash:H,lo:usize,keys:[u64;16],mut key_position:usize)->(u32,[u8;32],usize){\n'+prefix+'\n(index,leaf,key_position)\n}\n'
s+='\nfn dedup_fragment(idx:&mut[u32;16],val:&mut[[u8;32];16],mut d:usize,index:u32,leaf:[u8;32])->Result<usize,Error>{\nfor _ in 0..1 {\n'+dedup+'\n}\nOk(d)\n}\n';p.write_text(s)
p=E/'NKB_FRAGMENT_ASSOCIATION.json';x=json.loads(p.read_text());x['spans'] += [dict(body=t,sha256=hashlib.sha256(t.encode()).hexdigest(),source='crates/aspis-r1-cost-probe/src/candidate.rs') for t in [prefix,dedup]];p.write_text(json.dumps(x,indent=2)+'\n')
p=E/'NKB_harness.rs';s=p.read_text();s+='''
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(super::batch_leaf,logged_leaf)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn prefix_step(){
 let proof:[u8;57607]=kani::any();let keys:[u64;16]=kani::any();let pos:usize=kani::any();let batch:usize=kani::any();let tree:usize=kani::any();
 kani::assume(batch<2&&tree<3);let(lo,n)=if batch==0{(0,10)}else{(10,12)};kani::assume(pos<n);
 let key=keys[pos];kani::assume((key&255)<n as u64&&(key>>8)<262144);let ordinal=lo+(key&255)as usize;
 let reply:[u8;32]=kani::any();let calls=core::cell::Cell::new(0);let hash=LeafReply{proof:&proof,ordinal,tree,reply,calls:&calls};
 let(index,leaf,next)=prefix_fragment(&proof,tree,hash,lo,keys,pos);assert_eq!(calls.get(),1);assert_eq!(index,(key>>8)as u32);assert_eq!(next,pos+1);
 let k:usize=kani::any();kani::assume(k<32);
 #[cfg(not(NKB_invert))] assert_eq!(leaf[k],reply[k]);
 #[cfg(NKB_invert)] assert_ne!(leaf[k],reply[k]);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn dedup_step(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;let d:usize=kani::any();kani::assume(d<16);
 let index:u32=kani::any();let leaf:[u8;32]=kani::any();let same=d>0&&idx[d-1]==index;let good=!same||val[d-1]==leaf;
 let result=dedup_fragment(&mut idx,&mut val,d,index,leaf);
 if !good {assert!(matches!(result,Err(Error::Merkle)))} else {assert_eq!(result.unwrap(),if same{d}else{d+1})}
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);let write=good&&!same&&j==d;
 assert_eq!(idx[j],if write{index}else{before_i[j]});let expected=if write{leaf[k]}else{before_v[j][k]};
 #[cfg(not(NKB_invert))] assert_eq!(val[j][k],expected);
 #[cfg(NKB_invert)] assert_ne!(val[j][k],expected);
}
''';p.write_text(s)
for i,target in [(5,'prefix_step'),(6,'prefix_step'),(7,'dedup_step'),(8,'dedup_step')]:
 x=json.loads((E/'NKB_K003.json').read_text());x['attempt']=f'NKB_K{i:03d}';x['module']=target;x['collect']=[x['attempt']+'_validation'];x['command']=['python3','NKB_gate.py',x['attempt']+'.json'];x['expected_failure']=i%2==0;x['native_command'][-3]='verifier::candidate::NKB_native::'+target;x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKB_invert' if i%2==0 else '');x['expected_time']='Split '+target+' arbitrary-prestate cut; unchanged 90-second solver limit';(E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=2)+'\n')
print('NKB K004 timeout split into independent prefix and dedup windows')
