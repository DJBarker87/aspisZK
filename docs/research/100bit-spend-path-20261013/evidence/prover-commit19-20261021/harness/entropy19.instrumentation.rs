
#[cfg(any(kani,aeneas_ref))]
impl StateOnlyAttemptSecrets {
fn entropy_draw_step19()->Result<Option<Self>,StateOnlyAttemptEntropyError> {
            let mut bytes = Zeroizing::new([0u8; 96]);
            getrandom::fill(bytes.as_mut())?;

            let mut mask_nonce = [0u8; 32];
            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            mask_nonce.copy_from_slice(&bytes[..32]);
            field_mask_entropy.copy_from_slice(&bytes[32..64]);
            leaf_salt_seed.copy_from_slice(&bytes[64..]);

            if mask_nonce != [0; 32] && *field_mask_entropy != [0; 32] && *leaf_salt_seed != [0; 32]
            {
                return Ok(Some(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                }));
            }
    Ok(None)
}
}

#[cfg(kani)]
mod entropy19 {
 use super::*;
 static mut CALLS:usize=0;
 static mut RAW:[u8;96]=[0;96];
 fn draw(dest:&mut [u8])->Result<(),getrandom::Error> {
  assert_eq!(dest.len(),96);
  unsafe {CALLS+=1;
  dest[0]=RAW[0];
  dest[1]=RAW[1];
  dest[2]=RAW[2];
  dest[3]=RAW[3];
  dest[4]=RAW[4];
  dest[5]=RAW[5];
  dest[6]=RAW[6];
  dest[7]=RAW[7];
  dest[8]=RAW[8];
  dest[9]=RAW[9];
  dest[10]=RAW[10];
  dest[11]=RAW[11];
  dest[12]=RAW[12];
  dest[13]=RAW[13];
  dest[14]=RAW[14];
  dest[15]=RAW[15];
  dest[16]=RAW[16];
  dest[17]=RAW[17];
  dest[18]=RAW[18];
  dest[19]=RAW[19];
  dest[20]=RAW[20];
  dest[21]=RAW[21];
  dest[22]=RAW[22];
  dest[23]=RAW[23];
  dest[24]=RAW[24];
  dest[25]=RAW[25];
  dest[26]=RAW[26];
  dest[27]=RAW[27];
  dest[28]=RAW[28];
  dest[29]=RAW[29];
  dest[30]=RAW[30];
  dest[31]=RAW[31];
  dest[32]=RAW[32];
  dest[33]=RAW[33];
  dest[34]=RAW[34];
  dest[35]=RAW[35];
  dest[36]=RAW[36];
  dest[37]=RAW[37];
  dest[38]=RAW[38];
  dest[39]=RAW[39];
  dest[40]=RAW[40];
  dest[41]=RAW[41];
  dest[42]=RAW[42];
  dest[43]=RAW[43];
  dest[44]=RAW[44];
  dest[45]=RAW[45];
  dest[46]=RAW[46];
  dest[47]=RAW[47];
  dest[48]=RAW[48];
  dest[49]=RAW[49];
  dest[50]=RAW[50];
  dest[51]=RAW[51];
  dest[52]=RAW[52];
  dest[53]=RAW[53];
  dest[54]=RAW[54];
  dest[55]=RAW[55];
  dest[56]=RAW[56];
  dest[57]=RAW[57];
  dest[58]=RAW[58];
  dest[59]=RAW[59];
  dest[60]=RAW[60];
  dest[61]=RAW[61];
  dest[62]=RAW[62];
  dest[63]=RAW[63];
  dest[64]=RAW[64];
  dest[65]=RAW[65];
  dest[66]=RAW[66];
  dest[67]=RAW[67];
  dest[68]=RAW[68];
  dest[69]=RAW[69];
  dest[70]=RAW[70];
  dest[71]=RAW[71];
  dest[72]=RAW[72];
  dest[73]=RAW[73];
  dest[74]=RAW[74];
  dest[75]=RAW[75];
  dest[76]=RAW[76];
  dest[77]=RAW[77];
  dest[78]=RAW[78];
  dest[79]=RAW[79];
  dest[80]=RAW[80];
  dest[81]=RAW[81];
  dest[82]=RAW[82];
  dest[83]=RAW[83];
  dest[84]=RAW[84];
  dest[85]=RAW[85];
  dest[86]=RAW[86];
  dest[87]=RAW[87];
  dest[88]=RAW[88];
  dest[89]=RAW[89];
  dest[90]=RAW[90];
  dest[91]=RAW[91];
  dest[92]=RAW[92];
  dest[93]=RAW[93];
  dest[94]=RAW[94];
  dest[95]=RAW[95];
 }
  Ok(())
 }
 #[kani::proof]
 #[kani::unwind(98)]
 #[kani::stub(getrandom::fill,draw)]
 fn reject_block_0() {
  let raw:[u8;96]=[kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any()];
  kani::assume(raw[0]==0);
  kani::assume(raw[1]==0);
  kani::assume(raw[2]==0);
  kani::assume(raw[3]==0);
  kani::assume(raw[4]==0);
  kani::assume(raw[5]==0);
  kani::assume(raw[6]==0);
  kani::assume(raw[7]==0);
  kani::assume(raw[8]==0);
  kani::assume(raw[9]==0);
  kani::assume(raw[10]==0);
  kani::assume(raw[11]==0);
  kani::assume(raw[12]==0);
  kani::assume(raw[13]==0);
  kani::assume(raw[14]==0);
  kani::assume(raw[15]==0);
  kani::assume(raw[16]==0);
  kani::assume(raw[17]==0);
  kani::assume(raw[18]==0);
  kani::assume(raw[19]==0);
  kani::assume(raw[20]==0);
  kani::assume(raw[21]==0);
  kani::assume(raw[22]==0);
  kani::assume(raw[23]==0);
  kani::assume(raw[24]==0);
  kani::assume(raw[25]==0);
  kani::assume(raw[26]==0);
  kani::assume(raw[27]==0);
  kani::assume(raw[28]==0);
  kani::assume(raw[29]==0);
  kani::assume(raw[30]==0);
  kani::assume(raw[31]==0);
  unsafe {RAW=raw;CALLS=0;}
  let actual=StateOnlyAttemptSecrets::entropy_draw_step19();
  assert!(matches!(actual,Ok(None)));
  assert_eq!(unsafe{CALLS},1);
 }
 #[kani::proof]
 #[kani::unwind(98)]
 #[kani::stub(getrandom::fill,draw)]
 fn reject_block_1() {
  let raw:[u8;96]=[kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any()];
  kani::assume(raw[32]==0);
  kani::assume(raw[33]==0);
  kani::assume(raw[34]==0);
  kani::assume(raw[35]==0);
  kani::assume(raw[36]==0);
  kani::assume(raw[37]==0);
  kani::assume(raw[38]==0);
  kani::assume(raw[39]==0);
  kani::assume(raw[40]==0);
  kani::assume(raw[41]==0);
  kani::assume(raw[42]==0);
  kani::assume(raw[43]==0);
  kani::assume(raw[44]==0);
  kani::assume(raw[45]==0);
  kani::assume(raw[46]==0);
  kani::assume(raw[47]==0);
  kani::assume(raw[48]==0);
  kani::assume(raw[49]==0);
  kani::assume(raw[50]==0);
  kani::assume(raw[51]==0);
  kani::assume(raw[52]==0);
  kani::assume(raw[53]==0);
  kani::assume(raw[54]==0);
  kani::assume(raw[55]==0);
  kani::assume(raw[56]==0);
  kani::assume(raw[57]==0);
  kani::assume(raw[58]==0);
  kani::assume(raw[59]==0);
  kani::assume(raw[60]==0);
  kani::assume(raw[61]==0);
  kani::assume(raw[62]==0);
  kani::assume(raw[63]==0);
  unsafe {RAW=raw;CALLS=0;}
  let actual=StateOnlyAttemptSecrets::entropy_draw_step19();
  assert!(matches!(actual,Ok(None)));
  assert_eq!(unsafe{CALLS},1);
 }
 #[kani::proof]
 #[kani::unwind(98)]
 #[kani::stub(getrandom::fill,draw)]
 fn reject_block_2() {
  let raw:[u8;96]=[kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any(),kani::any()];
  kani::assume(raw[64]==0);
  kani::assume(raw[65]==0);
  kani::assume(raw[66]==0);
  kani::assume(raw[67]==0);
  kani::assume(raw[68]==0);
  kani::assume(raw[69]==0);
  kani::assume(raw[70]==0);
  kani::assume(raw[71]==0);
  kani::assume(raw[72]==0);
  kani::assume(raw[73]==0);
  kani::assume(raw[74]==0);
  kani::assume(raw[75]==0);
  kani::assume(raw[76]==0);
  kani::assume(raw[77]==0);
  kani::assume(raw[78]==0);
  kani::assume(raw[79]==0);
  kani::assume(raw[80]==0);
  kani::assume(raw[81]==0);
  kani::assume(raw[82]==0);
  kani::assume(raw[83]==0);
  kani::assume(raw[84]==0);
  kani::assume(raw[85]==0);
  kani::assume(raw[86]==0);
  kani::assume(raw[87]==0);
  kani::assume(raw[88]==0);
  kani::assume(raw[89]==0);
  kani::assume(raw[90]==0);
  kani::assume(raw[91]==0);
  kani::assume(raw[92]==0);
  kani::assume(raw[93]==0);
  kani::assume(raw[94]==0);
  kani::assume(raw[95]==0);
  unsafe {RAW=raw;CALLS=0;}
  let actual=StateOnlyAttemptSecrets::entropy_draw_step19();
  assert!(matches!(actual,Ok(None)));
  assert_eq!(unsafe{CALLS},1);
 }
}
