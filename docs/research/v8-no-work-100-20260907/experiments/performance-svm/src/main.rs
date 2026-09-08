//! Local simulation only. No RPC, no persisted keys, no pool settlement.
use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_instruction::{Instruction,account_meta::AccountMeta};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_signer::Signer;
use solana_transaction::Transaction;
fn main(){
    let args:Vec<_>=std::env::args().collect();
    assert_eq!(args.len(),3,"usage: performance-svm program.so fixture-dir");
    let elf=std::fs::read(&args[1]).unwrap();
    let program=Address::new_from_array([71;32]);
    let keys=[Address::new_from_array([72;32]),Address::new_from_array([73;32]),Address::new_from_array([74;32])];
    for limit in [1_400_000u64,100_000_000] {
        for seed in [1,2,3] {
            let original=std::fs::read(format!("{}/proof-{seed}.bin",args[2])).unwrap();
            for case in ["honest","bad-fixed","bad-leaf","bad-frontier","truncated"] {
                if limit==1_400_000&&case!="honest"{continue;}
                let mut proof=original.clone();
                match case {"bad-fixed"=>proof[0]^=1,"bad-leaf"=>proof[11228]^=1,"bad-frontier"=>{let n=proof.len();proof[n-1]^=1;},"truncated"=>{proof.pop();},_=>{}}
                let public=std::fs::read(format!("{}/public.bin",args[2])).unwrap();
                let transition=std::fs::read(format!("{}/transition.bin",args[2])).unwrap();
                let binding=std::fs::read(format!("{}/binding.bin",args[2])).unwrap();
                let mut svm=LiteSVM::new();
                let payer=Keypair::new();svm.airdrop(&payer.pubkey(),1_000_000_000).unwrap();
                let mut budget=ComputeBudget::new_with_defaults(false);
                budget.compute_unit_limit=limit;budget.heap_size=256*1024;
                svm=svm.with_compute_budget(budget);
                if let Err(e)=svm.add_program(program,&elf){println!("{}",serde_json::json!({"load_error":format!("{e:?}")}));return;}
                let data=[proof,public,transition];
                for(i,d)in data.iter().enumerate(){svm.set_account(keys[i],Account{lamports:100_000_000,data:d.clone(),owner:program,executable:false,rent_epoch:0}).unwrap();}
                let ix=Instruction{program_id:program,accounts:keys.iter().map(|k|AccountMeta::new_readonly(*k,false)).collect(),data:binding};
                let tx=Transaction::new(&[&payer],Message::new(&[ix],Some(&payer.pubkey())),svm.latest_blockhash());
                let result=svm.simulate_transaction(tx);
                let(ok,error,meta)=match result{Ok(r)=>(true,None,r.meta),Err(r)=>(false,Some(format!("{:?}",r.err)),r.meta)};
                for(i,d)in data.iter().enumerate(){assert_eq!(svm.get_account(&keys[i]).unwrap().data,*d);}
                println!("{}",serde_json::json!({"seed":seed,"case":case,"cu_limit":limit,"accepted":ok,"error":error,"cu":meta.compute_units_consumed,"logs":meta.logs,"unchanged_accounts":true,"scope":"isolated research verifier; no pool settlement","diagnostic_above_transaction_limit":limit>1_400_000}));
                if limit>1_400_000 {
                    assert_eq!(ok,case=="honest","diagnostic budget must reach the expected endpoint");
                    if case!="honest" {assert!(error.as_ref().unwrap().contains("Custom("),"resource exhaustion is not a checked malformed-proof rejection");}
                }
            }
        }
    }
}
