"""Generate a release-only local-owner differential; not whole proofs/retry owner."""
from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[2]
s=(R/'crates/aspis-prover/src/state_only_entropy.rs').read_text()
a=s.index('    pub fn generate_for_mask_nonce(');b=s.index('    pub fn mask_nonce(',a)
old=s[a:b].replace('pub fn generate_for_mask_nonce(', 'pub fn old(').replace('mask_nonce: [u8; 32],','mask_nonce: [u8; 32],\n        tape: &mut Recorder,',1).replace('getrandom::fill(bytes.as_mut())?;', 'tape.draw(&mut bytes)?;')
out='''use super::*;
impl From<u8> for StateOnlyAttemptEntropyError { fn from(e:u8)->Self { Self::Os(e) } }
struct Recorder { replies: Vec<([u8;64],Result<(),u8>)>, used: usize, inputs: Vec<[u8;64]> }
impl Recorder {
fn draw(&mut self,b:&mut [u8;64])->Result<(),u8> {
 self.inputs.push(*b);
 assert!(self.used<self.replies.len());
 let (block,r)=self.replies[self.used];self.used+=1;*b=block;r
}
}
impl Draw64 for Recorder {
fn fill(mut self,b:&mut [u8;64])->(Self,Result<(),u8>) { let r=self.draw(b);(self,r) }
}
impl StateOnlyAttemptSecrets {
'''+old+'''}
fn view(r:Result<StateOnlyAttemptSecrets,StateOnlyAttemptEntropyError>)->Result<([u8;32],[u8;32],[u8;32]),StateOnlyAttemptEntropyError> {
 r.map(|s|(s.mask_nonce,*s.field_mask_entropy,*s.leaf_salt_seed))
}
#[test]
fn same_event_local_owner() {
 let mut cases=0;
 // Every zero-retry prefix, all terminal errors, both one-half failures,
 // and cap16. Every error reply carries nonzero partial buffer writes.
 for nonce in [[0u8;32],[7u8;32]] {
 for rejected in 0..=16 {
 for terminal in 0..=256u16 {
 for bad_half in 0..3 {
 let mut bad=[0u8;64];
 if bad_half==1 {bad[..32].fill(3);}
 if bad_half==2 {bad[32..].fill(4);}
 let mut replies=vec![(bad,Ok(()));rejected];
 replies.push(([9u8;64], if terminal==256 {Ok(())} else {Err(terminal as u8)}));
 let mk=||Recorder{replies:replies.clone(),used:0,inputs:vec![]};
 let mut old=mk();let a=StateOnlyAttemptSecrets::old(nonce,&mut old);
 let (new,b)=StateOnlyAttemptSecrets::generate_with(nonce,mk());
 assert_eq!(view(a),view(b));assert_eq!(old.used,new.used);
 assert_eq!(old.inputs,new.inputs);assert!(new.inputs.iter().all(|x|*x==[0;64]));
 assert_eq!(&old.replies[..old.used],&new.replies[..new.used]);
 cases+=1;
 }}}}
 assert_eq!(cases,26214);
 println!("local entropy owner same-event cases={cases}; no outer retry/body/ledger/whole-proof coverage");
}
'''
(D/'prototype/runtime.rs').write_text(out)
p=D/'prototype/lib.rs';text=p.read_text();text+='\n#[cfg(test)]\nmod runtime;\n';p.write_text(text)
(D/'runtime-binding.json').write_text(json.dumps({'old_source_owner_sha256':hashlib.sha256(s[a:b].encode()).hexdigest(),'old_adapter':['only extra &mut Recorder argument and substitution of getrandom::fill with Recorder::draw','From<u8> models error tag only, no native error-layout claim'],'coverage':'local 64-byte entropy owner only, 26214 finite scenarios; no whole proofs, outer owner, ledger, or E1 distribution','generated_runtime_sha256':hashlib.sha256(out.encode()).hexdigest()},indent=2)+'\n')
