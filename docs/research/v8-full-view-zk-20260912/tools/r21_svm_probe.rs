//! Measures only the R21 ordinary+image pilot. Never a complete Aspis gate.
use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_instruction::{account_meta::AccountMeta,Instruction};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_signer::Signer;
use solana_transaction::Transaction;
fn main(){
    let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),4,"elf helper.bin native|helper");
    let native=match a[3].as_str(){"native"=>true,"helper"=>false,_=>panic!("mode")};
    let elf=std::fs::read(&a[1]).unwrap();let original=std::fs::read(&a[2]).unwrap();assert!(original.len()>448);
    let cases:&[&str]=if native{&["honest","wrong-output"]}else{&["honest","wrong-output","wrong-input","wrong-context","wrong-first-message","wrong-last-message","noncanonical-input","noncanonical-message","truncated","trailing"]};
    for cap in [1_000_000u64,100_000_000]{for &case in cases{
        let mut bytes=original.clone();let end=bytes.len();
        match case{
            "wrong-output"=>bytes[384]^=1,"wrong-input"=>bytes[0]^=1,"wrong-context"=>bytes[400]^=1,
            "wrong-first-message"=>bytes[432]^=1,"wrong-last-message"=>bytes[end-16]^=1,
            "noncanonical-input"=>bytes[..4].copy_from_slice(&2147483647u32.to_le_bytes()),
            "noncanonical-message"=>bytes[432..436].copy_from_slice(&2147483647u32.to_le_bytes()),
            "truncated"=>{bytes.pop();},"trailing"=>bytes.push(0),"honest"=>(),_=>panic!("case")
        }
        let mut budget=ComputeBudget::new_with_defaults(false);budget.compute_unit_limit=cap;budget.heap_size=262144;
        let mut svm=LiteSVM::new().with_compute_budget(budget);
        let payer=Keypair::new();svm.airdrop(&payer.pubkey(),1_000_000_000).unwrap(); // simulator identity only
        let program=Address::new_from_array([71;32]);let key=Address::new_from_array([72;32]);
        svm.add_program(program,&elf).unwrap();
        svm.set_account(key,Account{lamports:100_000_000,data:bytes.clone(),owner:program,executable:false,rent_epoch:0}).unwrap();
        let ix=Instruction{program_id:program,accounts:vec![AccountMeta::new_readonly(key,false)],data:vec![]};
        let tx=Transaction::new(&[&payer],Message::new(&[ix],Some(&payer.pubkey())),svm.latest_blockhash());
        let (accepted,error,meta)=match svm.simulate_transaction(tx){Ok(r)=>(true,None,r.meta),Err(r)=>(false,Some(format!("{:?}",r.err)),r.meta)};
        let custom=error.as_ref().is_some_and(|s|s.contains("Custom(21)")||s.contains("InvalidInstructionData")||s.contains("InvalidArgument"));
        let resource=error.as_ref().is_some_and(|s|s.contains("ProgramFailedToComplete")||s.contains("ComputationalBudgetExceeded"));
        assert_eq!(svm.get_account(&key).unwrap().data,bytes);
        println!("{}",serde_json::json!({"scope":"ordinary+image arithmetic pilot ONLY","mode":a[3],"case":case,"cu_limit":cap,"heap_bytes":262144,"accepted":accepted,"checked_rejection":custom,"resource_failure":resource,"error":error,"cu":meta.compute_units_consumed,"logs":meta.logs,"complete_aspis_verifier":false}));
    }}
}
