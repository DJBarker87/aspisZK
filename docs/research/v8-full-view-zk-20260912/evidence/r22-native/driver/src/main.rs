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
    let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),4,"elf wire reference|scalar");
    let mode=match a[3].as_str(){"reference"=>0,"scalar"=>1,_=>panic!("mode")};
    let elf=std::fs::read(&a[1]).unwrap();let original=std::fs::read(&a[2]).unwrap();assert_eq!(original.len(),400);
    let traced=std::env::var_os("SBF_TRACE_DIR").is_some();
    let cases:&[&str]=if traced{&["honest"]}else{&["honest","wrong-output","noncanonical-input","truncated"]};
    let caps:&[u64]=if traced{&[1_000_000]}else{&[1_000_000,100_000_000]};
    for &cap in caps {for &case in cases {
        let mut bytes=original.clone();match case{"honest"=>(),"wrong-output"=>bytes[384]^=1,"noncanonical-input"=>bytes[..4].copy_from_slice(&2147483647u32.to_le_bytes()),"truncated"=>{bytes.pop();},_=>panic!()}
        let mut budget=ComputeBudget::new_with_defaults(false);budget.compute_unit_limit=cap;budget.heap_size=262144;
        let mut svm=LiteSVM::new().with_compute_budget(budget);let payer=Keypair::new();svm.airdrop(&payer.pubkey(),1_000_000_000).unwrap();
        let program=Address::new_from_array([73;32]);let key=Address::new_from_array([74;32]);svm.add_program(program,&elf).unwrap();
        svm.set_account(key,Account{lamports:100_000_000,data:bytes.clone(),owner:program,executable:false,rent_epoch:0}).unwrap();
        let ix=Instruction{program_id:program,accounts:vec![AccountMeta::new_readonly(key,false)],data:vec![mode]};
        let tx=Transaction::new(&[&payer],Message::new(&[ix],Some(&payer.pubkey())),svm.latest_blockhash());
        let (accepted,error,meta)=match svm.simulate_transaction(tx){Ok(r)=>(true,None,r.meta),Err(r)=>(false,Some(format!("{:?}",r.err)),r.meta)};
        assert_eq!(svm.get_account(&key).unwrap().data,bytes);
        let checked=error.as_ref().is_some_and(|e|e.contains("Custom(22)")||e.contains("InvalidInstructionData"));
        let resource=error.as_ref().is_some_and(|e|e.contains("ProgramFailedToComplete")||e.contains("ComputationalBudgetExceeded"));
        println!("{}",serde_json::json!({"mode":a[3],"case":case,"cap":cap,"cu":meta.compute_units_consumed,"accepted":accepted,"error":error,"checked_rejection":checked,"resource_failure":resource,"heap_bytes":262144,"register_tracing":traced,"logs":meta.logs,"complete_aspis_verifier":false}));
    }}
}
