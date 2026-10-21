#[cfg(all(test,aeneas_ref))]
mod semantic_tests20 {
    use super::*;
    use alloc::vec;
    use core::cell::RefCell;
    #[derive(Clone,Copy)]
    struct TraceHash<'a>(&'a RefCell<Vec<(Vec<u8>,[u8;32])>>);
    impl Digest32 for TraceHash<'_> {
        fn digest(&self,parts:&[&[u8]])->[u8;32] {
            let mut trace=self.0.borrow_mut();
            let answer=core::array::from_fn(|i| (trace.len() as u8).wrapping_mul(17).wrapping_add(i as u8));
            let mut address=Vec::new();for part in parts {address.extend_from_slice(part);}
            trace.push((address,answer));answer
        }
    }
    fn compare(row:u8,next:u8,framed:&[u8]) {
        let source_log=RefCell::new(Vec::new());let owned_log=RefCell::new(Vec::new());
        let state=core::array::from_fn(|i|i as u8);
        let mut source=SemanticTranscript{state,hash:TraceHash(&source_log),next_row:next};
        let owned=SemanticTranscript{state,hash:TraceHash(&owned_log),next_row:next};
        let expected=source.semantic(row,framed);
        let (actual,after)=semantic20::semantic(owned,row,framed.to_vec());
        assert_eq!(actual,expected);assert_eq!(after.state,source.state);assert_eq!(after.next_row,source.next_row);
        assert_eq!(*source_log.borrow(),*owned_log.borrow());
    }
    #[test]
    fn all_rows_and_errors() {
        for row in 0..27 {
            let (_,size)=row_shape(row).unwrap();let payload=vec![0;size];let frame=record(row,&payload).unwrap();
            compare(row,row,&frame);compare(row,row.wrapping_add(1),&frame);
            compare(row,row,&frame[..frame.len()-1]);
            let mut tag=frame.clone();tag[0]^=128;compare(row,row,&tag);
            let mut length=frame.clone();length[1]^=1;compare(row,row,&length);
            if row>=14 {
                for value in 0..size/32 {
                    let mut high=frame.clone();high[5+32*value+16]=1;compare(row,row,&high);
                    let mut noncanonical=frame.clone();noncanonical[5+32*value..9+32*value].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
                    compare(row,row,&noncanonical);
                }
            }
        }
        compare(255,255,&[]);
    }
    #[test]
    fn complete_twenty_five_rows() {
        let records:Vec<Vec<u8>>=(0..25).map(|row|record(row,&vec![0;row_shape(row).unwrap().1]).unwrap()).collect();
        for fail in 0..=25 {
            let mut records=records.clone();if fail<25 {records[fail][0]^=128;}
            let source_log=RefCell::new(Vec::new());let owned_log=RefCell::new(Vec::new());let state=[7;32];
            let mut source=SemanticTranscript{state,hash:TraceHash(&source_log),next_row:0};
            let owned=SemanticTranscript{state,hash:TraceHash(&owned_log),next_row:0};
            let mut expected=[QM31::ZERO;25];let mut error=None;
            for row in 0..25 {match source.semantic(row as u8,&records[row]) {Ok(x)=>expected[row]=x,Err(e)=>{error=Some(e);break;}}}
            let (actual,after)=semantic20::rows(owned,records,0,[QM31::ZERO;25]);
            assert_eq!(actual,match error {None=>Ok(expected),Some(e)=>Err(e)});
            assert_eq!(after.state,source.state);assert_eq!(after.next_row,source.next_row);
            assert_eq!(*source_log.borrow(),*owned_log.borrow());
        }
    }
}
