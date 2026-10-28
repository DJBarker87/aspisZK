from pathlib import Path
E=Path(__file__).resolve().parent;B=E.parent/'kani-mitig-20261028';p=E/'KMY_windows.rs';s=p.read_text()
s+='\ntrait Digest32 {fn digest(&self,parts:&[&[u8]])->[u8;32];}\n'
# Preserve original selected oracle definitions exactly.
lines=(B/'KMX_LPe_replay.rs.txt').read_text().splitlines()
s+='\n'.join(lines[283:285])+'\n'
lines=(B/'KMX_LPf_verifier.rs.txt').read_text().splitlines();s+='\n'.join(lines[3:5])+'\n'
t=(B/'KMX_LPi_verifier.rs.txt').read_text();start=t.index('#[derive(Clone,Copy)]\nstruct JoinedOracle');end=t.index('fn joined_digest_cut',start);s+=t[start:end]
s+='''
#[kani::proof] #[kani::unwind(33)]
fn KMY_digest_prefix_oracle(){
 let proof:[u8;3]=kani::any();let public:[u8;5]=kani::any();let answers:[[u8;32];3]=kani::any();
 let count=core::cell::Cell::new(0);let hash=Ordered{count:&count,proof:&proof,public:&public,answers};
 let hp=hash.digest(&[&proof]);let hu=hash.digest(&[&public]);assert_eq!(count.get(),2);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(hp[j],answers[0][j]);assert_eq!(hu[j],answers[1][j]);
}
#[kani::proof] #[kani::unwind(33)]
fn KMY_checksum_oracle(){
 let prefix:[u8;1736]=kani::any();let answer:[u8;32]=kani::any();let index:usize=kani::any();kani::assume(index<1736);
 let count=core::cell::Cell::new(2);let hash=Checksum{count:&count,prefix:&prefix,index,answer};
 let sum=hash.digest(&[b"UNPROVED:R1:checkpoint",&prefix]);assert_eq!(count.get(),3);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(sum[j],answer[j]);
}
fn joined_oracle<const PROOF:usize,const PUBLIC:usize>(){
 let proof=[0u8;PROOF];let public=[0u8;PUBLIC];let body:[u8;1736]=kani::any();let answers:[[u8;32];3]=kani::any();
 let selected:usize=kani::any();kani::assume(selected<1736);let count=core::cell::Cell::new(0);
 let hash=JoinedOracle{count:&count,proof:&proof,public:&public,body:&body,selected,answers};
 let hp=hash.digest(&[&proof]);let hu=hash.digest(&[&public]);
 let mut completed=body;
 // This is the pointwise relation proved for every selected byte by joined_digest.
 completed[selected]=joined_byte(&body,&answers,selected);
 let sum=hash.digest(&[b"UNPROVED:R1:checkpoint",&completed]);assert_eq!(count.get(),3);
 let j:usize=kani::any();kani::assume(j<32);assert_eq!(hp[j],answers[0][j]);assert_eq!(hu[j],answers[1][j]);assert_eq!(sum[j],answers[2][j]);
}
#[kani::proof] #[kani::unwind(33)] fn KMY_joined_oracle_small(){joined_oracle::<3,5>();}
#[kani::proof] #[kani::unwind(33)] fn KMY_joined_oracle_physical(){joined_oracle::<57607,1880>();}
#[kani::proof] #[kani::unwind(9)]
fn KMY_local_parse_reject(){
 let raw:[u32;8]=kani::any();let bad:usize=kani::any();kani::assume(bad<8);kani::assume(raw[bad]>=0x7fff_ffff);
 let mut bytes=[0u8;32];for limb in 0..8{for byte in 0..4{bytes[4*limb+byte]=raw[limb].to_le_bytes()[byte];}}
 assert!(E::from_le_bytes(&bytes).is_none());
}
'''
p.write_text(s)
