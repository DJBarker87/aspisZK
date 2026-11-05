from pathlib import Path
E=Path(__file__).resolve().parent
member=' || '.join(f'(len>{i} && accepted[{i}]==candidate)' for i in range(22))
domain=' && '.join(f'accepted[{i}]<(1<<18)' for i in range(22))
s='''fn NHB_word_ref(accepted:[u32;22],len:usize,draws:usize,block:[u8;32],start:usize,window:usize)
 ->(bool,u32,usize,usize,usize,u32) {
 let candidate=u32::from_le_bytes([block[4*start],block[4*start+1],block[4*start+2],block[4*start+3]]) & ((1<<18)-1);
 let member='''+member+''';
 let halted=len==22 || draws==64;
 let value=if !halted && !member && window==len {candidate} else {accepted[window]};
 (halted,candidate,start+1,if halted || member {len}else{len+1},if halted{draws}else{draws+1},value)
}
#[kani::requires(len<=22 && draws<=64 && start<8 && window<22 && '''+domain+''')]
#[kani::ensures(|out| *out==NHB_word_ref(accepted,len,draws,block,start,window))]
fn NHB_native_word(accepted:[u32;22],len:usize,draws:usize,block:[u8;32],start:usize,window:usize)
 ->(bool,u32,usize,usize,usize,u32) {
 let mut copied=block;
 #[cfg(NHB_reply_corrupt)] {copied[0]^=1;}
 let mut scan=QueryScan{accepted,accepted_len:len,draws};let mut cursor=start;
 let (stop,word)=scan.NHB_cursor_word(&copied,&mut cursor);
 (stop,word,cursor,scan.accepted_len,scan.draws,scan.accepted[window])
}
#[kani::proof_for_contract(NHB_native_word)] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
'''+''.join(f'#[kani::stub_verified(NHB_contains_{n})]\n' for n in range(23))+'''fn NHB_native_word_contract() {
 let accepted:[u32;22]=kani::any();let len:usize=kani::any();let draws:usize=kani::any();
 let block:[u8;32]=kani::any();let start:usize=kani::any();let window:usize=kani::any();
 NHB_native_word(accepted,len,draws,block,start,window);
}
'''
(E/'NHB_word_contract.rs.txt').write_text(s)
