#[cfg(kani)]
mod caller_kani30 {
    use super::*;
    #[derive(Clone,Copy)] struct OpaqueOracle;
    impl Digest32 for OpaqueOracle {fn digest(&self,_:&[&[u8]])->[u8;32] {panic!("caller hashed outside its semantic callee")}}
    // Filled verbatim from the single native loop statement by install-kani.py.
    fn shipped_iteration<H:Digest32>(mut st:SemanticTranscript<H>, row:u8,
        r:&Records,mut sem:[K;25])->Result<(SemanticTranscript<H>,[K;25]),Error> {
        sem[row as usize]=st.semantic(row,&r.semantic[row as usize]).map_err(|_|Error::Semantic)?;
        Ok((st,sem))
    }
    fn checked_fields(row:u8,payload:Vec<u8>,value:usize)->Result<(),crate::r1_wire::Error> {
        let remaining=if row==14 {1} else {28};
        assert!(payload.len()<32*(remaining+1));
        assert_eq!(value,0);
        crate::r1_wire::fields29::finite(row,payload,value,remaining)
    }
    fn check<const N:usize,const ROW:u8>() {
        let x:[u32;4]=kani::any();
        let value=K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}};

        let row:u8=ROW;assert!(row<25);
        let next:u8=kani::any(); let initial:[u8;32]=kani::any();
        let sem=[
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
            K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}},
        ];
        let bytes:[u8;N]=kani::any();let len:usize=if N==0 {0} else {kani::any()};kani::assume(len<=N);
        let record=bytes[..len].to_vec();
        let state=crate::r1_wire::make_kani29(OpaqueOracle,initial,next);
        let mut records=vec![Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new(),Vec::new()];records[row as usize]=record.clone();
        let r=Records{c1_root:[0;32],semantic:records,
            y1:Vec::new(),inactive:[0;32],c0:Vec::new(),folded_root:[0;32],c1:Vec::new(),fin:Vec::new()};
        crate::r1_wire::context_kani30::setup(record.clone(),row,initial,next,value);
        let actual=shipped_iteration(state,row,&r,sem);
        assert_eq!(crate::r1_wire::context_kani30::count_reset(),1);
        let state=crate::r1_wire::make_kani29(OpaqueOracle,initial,next);
        let reference=owned29::iteration(state,row,r.semantic,sem);
        assert_eq!(crate::r1_wire::context_kani30::count_reset(),1);
        match (actual,reference) {
            (Ok((a,x)),Ok((b,y)))=>{assert_eq!(a.state(),b.state());assert_eq!(a.next_row(),b.next_row());let k:usize=kani::any();kani::assume(k<25);assert_eq!(x[k],y[k]);}
            (Err(a),Err(b))=>assert_eq!(a,b),
            _=>assert!(false),
        }
    }
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row00(){check::<37,0>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row01(){check::<37,1>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row02(){check::<37,2>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row03(){check::<37,3>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row04(){check::<37,4>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row05(){check::<37,5>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row06(){check::<37,6>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row07(){check::<37,7>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row08(){check::<37,8>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row09(){check::<37,9>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row10(){check::<37,10>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row11(){check::<37,11>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row12(){check::<37,12>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row13(){check::<37,13>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row14(){check::<37,14>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row15(){check::<901,15>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row16(){check::<901,16>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row17(){check::<901,17>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row18(){check::<901,18>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row19(){check::<901,19>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row20(){check::<901,20>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row21(){check::<901,21>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row22(){check::<901,22>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row23(){check::<901,23>()}
    #[kani::proof]
    #[kani::stub(crate::r1_wire::SemanticTranscript::semantic,crate::r1_wire::context_kani30::native)]
    #[kani::stub(crate::r1_wire::semantic20::semantic,crate::r1_wire::context_kani30::owned)]
    #[kani::unwind(40)] fn row24(){check::<901,24>()}
}
