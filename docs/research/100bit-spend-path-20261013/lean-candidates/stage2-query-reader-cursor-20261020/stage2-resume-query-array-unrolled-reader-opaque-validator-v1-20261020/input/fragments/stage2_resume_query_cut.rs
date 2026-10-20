fn validate_queries(queries:[u32;22])->Result<[u32;22],Error> {
    let mut i=0usize;
    while i<22 {
        if queries[i]>=1<<18 { return Err(Error::Checkpoint); }
        let mut j=0usize;
        while j<i {
            if queries[j]==queries[i] { return Err(Error::Checkpoint); }
            j+=1;
        }
        i+=1;
    }
    Ok(queries)
}
pub fn resume_read_queries(bytes:&[u8],at:usize)->Result<([u32;22],usize),Error> {
    let mut r=Reader{bytes,at};
    let q0=u32::from_le_bytes(r.raw());
    let q1=u32::from_le_bytes(r.raw());
    let q2=u32::from_le_bytes(r.raw());
    let q3=u32::from_le_bytes(r.raw());
    let q4=u32::from_le_bytes(r.raw());
    let q5=u32::from_le_bytes(r.raw());
    let q6=u32::from_le_bytes(r.raw());
    let q7=u32::from_le_bytes(r.raw());
    let q8=u32::from_le_bytes(r.raw());
    let q9=u32::from_le_bytes(r.raw());
    let q10=u32::from_le_bytes(r.raw());
    let q11=u32::from_le_bytes(r.raw());
    let q12=u32::from_le_bytes(r.raw());
    let q13=u32::from_le_bytes(r.raw());
    let q14=u32::from_le_bytes(r.raw());
    let q15=u32::from_le_bytes(r.raw());
    let q16=u32::from_le_bytes(r.raw());
    let q17=u32::from_le_bytes(r.raw());
    let q18=u32::from_le_bytes(r.raw());
    let q19=u32::from_le_bytes(r.raw());
    let q20=u32::from_le_bytes(r.raw());
    let q21=u32::from_le_bytes(r.raw());
    let queries=validate_queries([q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21])?;
    Ok((queries,r.at))
}
