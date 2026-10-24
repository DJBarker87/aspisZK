from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
s=(D/'prototype/lib.rs').read_text().split('#[cfg(test)]')[0]
s=s.replace('const ENTROPY_RETRY_LIMIT: usize = 16;', 'const ENTROPY_RETRY_LIMIT: usize = 1;')
r=(D/'prototype/runtime.rs').read_text();a=r.index('    pub fn old(');b=r.index('\nfn view(',a)
s+='\nimpl From<u8> for StateOnlyAttemptEntropyError {fn from(e:u8)->Self {Self::Os(e)}}\n'
s+='''
#[derive(Clone)]
struct Recorder {block:[u8;64], status:Result<(),u8>, draws:u16, input:[u8;64]}
impl Recorder {fn draw(&mut self,b:&mut [u8;64])->Result<(),u8> {
 self.input=*b;self.draws+=1;*b=self.block;self.status
}}
impl Draw64 for Recorder {fn fill(mut self,b:&mut [u8;64])->(Self,Result<(),u8>) {
 let r=self.draw(b);(self,r)
}}
impl StateOnlyAttemptSecrets {
'''+r[a:b]+'''
fn view(r:Result<StateOnlyAttemptSecrets,StateOnlyAttemptEntropyError>)->Result<([u8;32],[u8;32],[u8;32]),StateOnlyAttemptEntropyError> {
 r.map(|s|(s.mask_nonce,*s.field_mask_entropy,*s.leaf_salt_seed))
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn source_iteration_same_event() {
 let nonce:[u8;32]=kani::any();let block:[u8;64]=kani::any();
 let failed:bool=kani::any();let tag:u8=kani::any();let draws:u16=kani::any();
 kani::assume(draws<128);
 let p=Recorder{block,status:if failed {Err(tag)}else{Ok(())},draws,input:kani::any()};
 let mut left=p.clone();let a=StateOnlyAttemptSecrets::old(nonce,&mut left);
 let (right,b)=StateOnlyAttemptSecrets::generate_with(nonce,p);
 assert_eq!(view(a),view(b));assert_eq!(left.draws,right.draws);
 assert_eq!(left.input,right.input);assert_eq!(left.status,right.status);
 assert_eq!(left.block,right.block);
}
'''
(D/'iteration/lib.rs').write_text(s)
c=(D/'prototype/Cargo.toml').read_text().replace('prover-rw-rng-preflight','prover-rw-rng-iteration')+'\n[profile.dev]\nopt-level = 3\n'
(D/'iteration/Cargo.toml').write_text(c)
(D/'iteration-binding.json').write_text(json.dumps({'scope':'one iteration plus nonce admission; cap changed 16 to 1 only in isolated Kani cut; no full cap16 induction, native OS error layout, outer caller or ledger claim','source': 'source-map.json','old_adapter':'runtime-binding.json','iteration_sha256':hashlib.sha256(s.encode()).hexdigest(),'bounds':'arbitrary nonce, arbitrary full64 reply including partial error writes, all u8 error tags, prior draws<128; checked overflow paths; unwind66 (64-byte zeroization and memcmp require 65; prior34 failure retained)'},indent=2)+'\n')
