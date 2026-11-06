from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;raw=Path('crates/aspis-r1-cost-probe/src/candidate.rs').read_text();a=raw.index('    let nodes = slot(proof, s);');b=raw.index('\n}\n',a);body=raw[a:b]
p=E/'NKB_fragments.rs';p.write_text(p.read_text()+'\nfn padding_fragment<H:Digest32>(proof:&[u8],root:[u8;32],s:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,hash:H,count:usize)->Result<(),Error>{\n'+body+'\n}\n')
p=E/'NKB_FRAGMENT_ASSOCIATION.json';x=json.loads(p.read_text());x['spans'].append(dict(body=body,sha256=hashlib.sha256(body.encode()).hexdigest(),source='crates/aspis-r1-cost-probe/src/candidate.rs'));p.write_text(json.dumps(x,indent=2)+'\n')
p=E/'NKB_harness.rs';p.write_text(p.read_text()+'''
fn forbidden_verify<H:Digest32>(_:H,_:Arity,_:&[u8;32],_:&mut[u32;16],_:&mut[[u8;32];16],_:usize,_:&[u8])->bool{assert!(false,"no verify after nonzero first padding word");false}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(multiproof::verify_in_place,forbidden_verify)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn padding_first(){
 let proof:[u8;57607]=kani::any();let s:usize=kani::any();let count:usize=kani::any();kani::assume(s<6);kani::assume(count<SLOT_NODES[s]);
 let nonzero:usize=kani::any();kani::assume(nonzero<8);let start=compact::slot_offset(s)+32*count;kani::assume(proof[start+nonzero]!=0);
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let before_i=idx;let before_v=val;let d:usize=kani::any();kani::assume(d<=16);let root:[u8;32]=kani::any();
 let out=padding_fragment(&proof,root,s,&mut idx,&mut val,d,NoDigest,count);
 #[cfg(not(NKB_invert))] assert!(matches!(out,Err(Error::Parse)));
 #[cfg(NKB_invert)] assert!(!matches!(out,Err(Error::Parse)));
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);assert_eq!(idx[j],before_i[j]);assert_eq!(val[j][k],before_v[j][k]);
}
''')
for i in [9,10]:
 x=json.loads((E/'NKB_K005.json').read_text());x['attempt']=f'NKB_K{i:03d}';x['module']='padding_first';x['collect']=[x['attempt']+'_validation'];x['command']=['python3','NKB_gate.py',x['attempt']+'.json'];x['expected_failure']=i==10;x['native_command'][-3]='verifier::candidate::NKB_native::padding_first';x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKB_invert' if i==10 else '');x['expected_time']='Single nonzero first padding word, no complete scan or SHA';(E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=2)+'\n')
print('NKB first padding-word rejection cut and control prepared')
