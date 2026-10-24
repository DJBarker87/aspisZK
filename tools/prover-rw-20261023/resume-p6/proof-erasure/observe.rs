// Executed observation, not a contract assumption. Both sources use this code.
pub(super) fn run(nonce:[u8;32],entry:usize,i:usize) -> super::Observation {
    let request=ProverRwResumeP6Request {mask_nonce:nonce,retry:entry};
    let draw=request.draw();
    let (control,result)=draw.resume();
    let retry=match control {ProverRwResumeP6Control::More(next)=>Some((next.retry,next.mask_nonce[i])),ProverRwResumeP6Control::Done=>None};
    let result=match result {
        Err(StateOnlyAttemptEntropyError::Os(e))=>super::ObservedResult::Os(e),
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)=>super::ObservedResult::Exhausted,
        Ok(None)=>super::ObservedResult::More,
        Ok(Some(owner))=>{
            let bytes=(owner.mask_nonce[i],owner.field_mask_entropy[i],owner.leaf_salt_seed[i]);
            drop(owner);
            super::ObservedResult::Owner(bytes)
        }
    };
    super::Observation {retry,result}
}
