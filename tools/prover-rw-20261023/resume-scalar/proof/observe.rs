// Concrete executed projection, shared verbatim by both selected source modules.
pub fn run(nonce:[u8;32],entry:usize,j:usize,phase:fn(bool)) -> super::Projection {
    let request=ProverRwResumeScalarRequest {mask_nonce:nonce,retry:entry};
    let draw=request.draw();
    let (control,result)=draw.resume();
    let retry=match control {
        ProverRwResumeScalarControl::More(next)=>Some((next.retry,next.mask_nonce[j])),
        ProverRwResumeScalarControl::Done=>None,
    };
    let success=matches!(&result,Ok(Some(_)));
    phase(success);
    let result=match result {
        Err(StateOnlyAttemptEntropyError::Os(error))=>super::ResultProjection::Os(error),
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)=>super::ResultProjection::Exhausted,
        Ok(None)=>super::ResultProjection::More,
        Ok(Some(owner))=>{
            let projection=super::ResultProjection::Owner(
                owner.mask_nonce[j],owner.field_mask_entropy[j],owner.leaf_salt_seed[j]);
            // Distinct later disposal, after observing LIVE returned fields.
            drop(owner);
            projection
        },
    };
    super::Projection {retry,result}
}
