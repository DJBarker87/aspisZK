#[cfg(kani)]
mod fields_kani30 {
    use super::*;
    // Independent byte-level outcome. No field constructor or decoder.
    fn cell(bytes:&[u8])->bool {
        assert_eq!(bytes.len(),32);
        for i in 0..4 {
            let j=4*i;
            if u32::from_le_bytes([bytes[j],bytes[j+1],bytes[j+2],bytes[j+3]])>=0x7fffffff {return false;}
        }
        for i in 16..32 {if bytes[i]!=0 {return false;}}
        true
    }
    fn expected(row:u8,payload:&[u8])->Result<(),Error> {
        for i in 0..payload.len()/32 {
            if !cell(&payload[32*i..32*i+32]) {return Err(Error::NonCanonical{row,value:i});}
        }
        Ok(())
    }
    fn check<const N:usize>() {
        let bytes:[u8;N]=kani::any();let len:usize=kani::any();kani::assume(len<=N);
        let row:u8=kani::any();let payload=&bytes[..len];
        assert_eq!(validate_record_fields(row,payload),expected(row,payload));
    }
    #[kani::proof] #[kani::unwind(34)] fn one_cell(){check::<63>()}
    #[kani::proof] #[kani::unwind(34)] fn all_cells(){check::<927>()}
    #[kani::proof] #[kani::unwind(34)] fn exact_payload(){
        let bytes:[u8;896]=kani::any();let row:u8=kani::any();
        assert_eq!(validate_record_fields(row,&bytes),expected(row,&bytes));
    }
    #[kani::proof] #[kani::unwind(34)] fn owned_payload(){
        let bytes:[u8;896]=kani::any();let row:u8=kani::any();
        assert_eq!(fields29::finite(row,bytes.to_vec(),0,28),expected(row,&bytes));
    }
    #[kani::proof] #[kani::unwind(34)] fn owned_one_cell(){
        let bytes:[u8;32]=kani::any();let row:u8=kani::any();
        assert_eq!(fields29::finite(row,bytes.to_vec(),0,1),expected(row,&bytes));
    }
}
