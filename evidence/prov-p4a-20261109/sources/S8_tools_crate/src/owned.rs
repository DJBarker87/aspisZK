// Reference only. Same scalar order and checked arithmetic as frozen source.
pub fn scalar_owned(raw:u64,limb:u32,basis:u32,flush:bool)->u64 {
    let updated=raw+u64::from(limb)*u64::from(basis);
    if flush {(updated&0x7fff_ffff)+(updated>>31)} else {updated}
}
pub fn residue_owned(row:[u64;4],power:K,basis:M31,flush:bool)->[u64;4] {
    [scalar_owned(row[0],power.c0.a.0,basis.0,flush),
     scalar_owned(row[1],power.c0.b.0,basis.0,flush),
     scalar_owned(row[2],power.c1.a.0,basis.0,flush),
     scalar_owned(row[3],power.c1.b.0,basis.0,flush)]
}
pub fn value_owned(row:[u64;4])->K {
    K{c0:CM31{a:M31::reduce_u64(row[0]),b:M31::reduce_u64(row[1])},
      c1:CM31{a:M31::reduce_u64(row[2]),b:M31::reduce_u64(row[3])}}
}
pub fn finish_owned(raw:Vec<[u64;4]>,mut weights:Vec<K>)->Vec<K> {
    let mut index=0;
    while index<weights.len() {
        weights[index]=value_owned(raw[index]);
        index+=1;
    }
    weights
}
pub fn check_values_owned(compact:&[u8])->Result<(),CodecError> {
    let mut index=0;
    while index<compact.len()/16 {
        let at=index*16;
        K::from_le_bytes(&compact[at..at+16]).ok_or(CodecError::NonCanonical)?;
        index+=1;
    }
    Ok(())
}
