//! UNPROVED R1 COST PROBE. Local LiteSVM measurement only.
use anyhow::{anyhow,ensure,Result};
use litesvm::LiteSVM;
use serde_json::{json,Value};
use sha2::{Digest,Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{account_meta::AccountMeta,Instruction};
use solana_keypair::Keypair;
use solana_signer::Signer;
use solana_transaction::Transaction;
use std::{env,fs,path::Path,time::Instant};
const LIMIT:u32=1_400_000;
fn sha(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn write(path:&Path,v:&Value)->Result<()> {ensure!(!path.exists(),"unchanged measurement rerun forbidden: {}",path.display());fs::write(path,serde_json::to_string_pretty(v)?+"\n")?;Ok(())}
fn markers(logs:&[String])->Vec<Value>{
    let mut out=vec![];
    for pair in logs.windows(2){if let Some(label)=pair[0].strip_prefix("Program log: r1:") {if let Some(rest)=pair[1].strip_prefix("Program consumption: "){if let Some(rem)=rest.split_whitespace().next().and_then(|s|s.parse::<u64>().ok()){out.push(json!({"phase":label,"remaining_cu":rem}));}}}}
    out
}
fn main()->Result<()> {
    ensure!(!cfg!(debug_assertions));let args:Vec<_>=env::args().collect();
    let diagnostic=match args[1].as_str(){"diagnostic"=>true,"acceptance"=>false,_=>return Err(anyhow!("mode"))};
    let elf=fs::read(&args[2])?;let dir=Path::new(&args[3]);let fixture=&args[4];let k:usize=args[5].parse()?;ensure!(k<=22);
    let fixtures=dir.join("fixtures");let proof=fs::read(fixtures.join(format!("{fixture}.proof.bin")))?;let public=fs::read(fixtures.join(format!("{fixture}.public.bin")))?;
    let meta:Value=serde_json::from_slice(&fs::read(fixtures.join(format!("{fixture}.fixture.json")))?)?;
    ensure!(meta["proof_sha256"]==sha(&proof)&&meta["public_sha256"]==sha(&public));
    // CKP2: rho, rho powers and final weights live in QM31.
    let checkpoint_len=744+16*if proof[8]==1 {256}else{64};
    let key_path=fixtures.join("litesvm-payer.json");let payer=if key_path.exists(){let b:Vec<u8>=serde_json::from_slice(&fs::read(&key_path)?)?;Keypair::try_from(b.as_slice())?}else{
        use std::{io::Write,os::unix::fs::OpenOptionsExt};let p=Keypair::new();fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(&key_path)?.write_all(serde_json::to_string(&p.to_bytes().to_vec())?.as_bytes())?;p
    };
    let out=dir.join("measurements");fs::create_dir_all(&out)?;
    let budget=if diagnostic {200_000_000u64}else{LIMIT as u64};let mode=if diagnostic {"diagnostic"}else{"acceptance"};
    let program=Address::new_from_array([0xa1;32]);let proof_key=Address::new_from_array([0xa2;32]);let public_key=Address::new_from_array([0xa3;32]);let checkpoint_key=Address::new_from_array([0xa4;32]);
    let mut first=[None,None];let mut completed=[true,true];
    for run in 1..=if diagnostic {1}else{5} {
        let mut svm=LiteSVM::new();
        if diagnostic {let nesting=LiteSVM::mainnet_feature_set().is_active(&agave_feature_set::raise_cpi_nesting_limit_to_8::ID);svm=svm.with_compute_budget(ComputeBudget{compute_unit_limit:budget,heap_size:256*1024,..ComputeBudget::new_with_defaults(nesting)});}
        svm.airdrop(&payer.pubkey(),1_000_000_000).map_err(|e|anyhow!("airdrop: {e:?}"))?;svm.add_program(program,&elf).map_err(|e|anyhow!("load: {e:?}"))?;
        for (key,data) in [(proof_key,proof.clone()),(public_key,public.clone()),(checkpoint_key,vec![0;checkpoint_len])]{svm.set_account(key,Account{lamports:100_000_000,data,owner:program,executable:false,rent_epoch:0})?;}
        let mut origin="same run tx1";
        for transaction in 1..=2usize {
            let file=out.join(format!("{fixture}-{mode}-k{k}-tx{transaction}-run{run}.json"));ensure!(!file.exists(),"unchanged measurement rerun forbidden");
            let start=Instant::now();let ix=Instruction{program_id:program,accounts:vec![AccountMeta::new_readonly(proof_key,false),AccountMeta::new_readonly(public_key,false),AccountMeta::new(checkpoint_key,false)],data:if transaction==1 {vec![1,k as u8]}else{vec![2]}};
            let instructions=[ComputeBudgetInstruction::set_compute_unit_limit(LIMIT),ComputeBudgetInstruction::request_heap_frame(256*1024),ix];
            let tx=Transaction::new_signed_with_payer(&instructions,Some(&payer.pubkey()),&[&payer],svm.latest_blockhash());
            let result=match svm.send_transaction(tx){Ok(m)=>(None,m),Err(e)=>(Some(format!("{:?}",e.err)),e.meta)};
            let unchanged=svm.get_account(&proof_key).unwrap().data==proof&&svm.get_account(&public_key).unwrap().data==public;
            let phase_markers=markers(&result.1.logs);
            let verifier_cu=result.1.logs.iter().find_map(|l|l.strip_prefix(&format!("Program {program} consumed "))?.split_whitespace().next()?.parse::<u64>().ok());
            let heap=result.1.logs.windows(2).find_map(|w|{if w[0]!="Program log: r1:heap-high-water" {return None;}let h=w[1].strip_prefix("Program log: ")?.split(',').next()?.trim().strip_prefix("0x")?;u64::from_str_radix(h,16).ok()});
            let signature=(result.0.clone(),verifier_cu,phase_markers.clone());let identical=first[transaction-1].as_ref().map_or(true,|x|x==&signature);first[transaction-1].get_or_insert(signature);
            let checkpoint=svm.get_account(&checkpoint_key).unwrap().data;
            let record=json!({"label":if diagnostic {"UNPROVED COST PROBE — DIAGNOSTIC elevated CU"}else{"UNPROVED COST PROBE — acceptance attempt at 1,400,000 CU"},"fixture":fixture,"variant":proof[8],"k":k,"transaction":transaction,"run":run,"source_revision":env::var("ASPIS_SOURCE_REVISION")?,"elf_sha256":sha(&elf),"proof_sha256":sha(&proof),"proof_bytes":proof.len(),"checkpoint_bytes":checkpoint.len(),"checkpoint_sha256":sha(&checkpoint),"checkpoint_origin":if transaction==1 {"zero-initialized"}else{origin},"runtime":{"litesvm":"0.16.0","agave":"4.2.1","limit_cu":budget,"instruction_limit_cu":LIMIT,"heap_bytes":262144},"execution":{"error":result.0,"cu":result.1.compute_units_consumed,"logs":result.1.logs},"verifier_cu":verifier_cu,"verifier_completed":result.0.is_none(),"phase_markers":phase_markers,"sbf_heap_high_water_bytes":heap,"proof_and_public_unchanged":unchanged,"identical_to_first_run":identical,"wall_seconds":start.elapsed().as_secs_f64()});
            write(&file,&record)?;
            ensure!(unchanged&&identical,"measurement mismatch");ensure!(heap.map_or(true,|h|h<=262144),"STOP: heap exceeds 256 KiB");
            std::println!("{fixture} {mode} k={k} tx{transaction} run{run}: CU={verifier_cu:?}, completed={}, heap={heap:?}",result.0.is_none());
            completed[transaction-1]&=result.0.is_none();
            if diagnostic {ensure!(result.0.is_none(),"DIAGNOSTIC did not complete");if transaction==1 {let path=out.join(format!("{fixture}-diagnostic-k{k}-checkpoint.bin"));ensure!(!path.exists());fs::write(path,&checkpoint)?;}}
            else if transaction==1&&result.0.is_some() {
                // Measure tx2 in isolation from the matching completed diagnostic
                // checkpoint. This does not count as a successful transaction pair.
                let checkpoint=fs::read(out.join(format!("{fixture}-diagnostic-k{k}-checkpoint.bin")))?;
                svm.set_account(checkpoint_key,Account{lamports:100_000_000,data:checkpoint,owner:program,executable:false,rent_epoch:0})?;origin="matching completed diagnostic tx1; acceptance tx1 failed";
            }
        }
    }
    write(&out.join(format!("{fixture}-{mode}-k{k}-summary.json")),&json!({"label":"UNPROVED COST PROBE","mode":mode,"k":k,"completed_all_runs":completed,"both_transactions_completed_all_runs":completed==[true,true]}))?;Ok(())
}
