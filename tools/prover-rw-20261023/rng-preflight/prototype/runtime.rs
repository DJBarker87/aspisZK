use super::*;
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
    pub fn old(
        mask_nonce: [u8; 32],
        tape: &mut Recorder,
    ) -> Result<Self, StateOnlyAttemptEntropyError> {
        let limit=ENTROPY_RETRY_LIMIT;

        if !entropy_nonzero32(&mask_nonce) {
            return Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock);
        }
        let mut retry=0;
        while retry<limit {
            let mut bytes = Zeroizing::new([0u8; 64]);
            tape.draw(&mut bytes)?;

            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            field_mask_entropy.copy_from_slice(&bytes[..32]);
            leaf_salt_seed.copy_from_slice(&bytes[32..]);
            if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed) {
                return Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                });
            }
            retry+=1;
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }

}
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
