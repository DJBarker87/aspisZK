//! FUTURE-VERSION EXPERIMENT. Local LiteSVM measurement of the single-invocation
//! verifiers against the pinned two-transaction pair, all in one ELF built
//! WITHOUT `pool-adapter` (three accounts: proof, public statement, checkpoint).
//! Diagnostic runs use an elevated compute limit and are labelled as such; the
//! acceptance runs use the real 1,400,000 CU transaction limit.
//!
//! usage: fused_probe <elf> <proof.bin> <public.bin> <out.json> <label>
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
use std::{env,fs,path::Path};
const LIMIT:u32=1_400_000;
const DIAGNOSTIC:u64=200_000_000;
fn sha(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
/// (label, remaining CU) at each `r1:` marker, and the consumed CU between
/// consecutive markers (the first interval starts at the program's entry).
fn phases(logs:&[String],limit:u64)->Vec<Value>{
    let mut out=vec![];let mut previous=limit;
    for pair in logs.windows(2){
        if let Some(label)=pair[0].strip_prefix("Program log: r1:") {
            if let Some(rest)=pair[1].strip_prefix("Program consumption: "){
                if let Some(rem)=rest.split_whitespace().next().and_then(|s|s.parse::<u64>().ok()){
                    out.push(json!({"phase":label,"remaining_cu":rem,"interval_cu":previous.saturating_sub(rem)}));previous=rem;
                }
            }
        }
    }
    out
}
struct Run{error:Option<String>,cu:u64,program_cu:Option<u64>,logs:Vec<String>,checkpoint:Vec<u8>}
fn main()->Result<()> {
    ensure!(!cfg!(debug_assertions),"release build only");
    let args:Vec<_>=env::args().collect();ensure!(args.len()==6,"usage: fused_probe <elf> <proof> <public> <out.json> <label>");
    let elf=fs::read(&args[1])?;let proof=fs::read(&args[2])?;let public=fs::read(&args[3])?;let out=Path::new(&args[4]);let label=&args[5];
    ensure!(!out.exists(),"unchanged measurement rerun forbidden: {}",out.display());
    ensure!(proof.len()==57_607,"compact S2 proof expected");
    let checkpoint_len=744+16*64;
    let program=Address::new_from_array([0xa1;32]);let proof_key=Address::new_from_array([0xa2;32]);let public_key=Address::new_from_array([0xa3;32]);let checkpoint_key=Address::new_from_array([0xa4;32]);
    let payer=Keypair::new();
    let send_with=|proof_data:&[u8],data:Vec<u8>,checkpoint:Vec<u8>,diagnostic:bool|->Result<Run> {
        let mut svm=LiteSVM::new();
        if diagnostic {let nesting=LiteSVM::mainnet_feature_set().is_active(&agave_feature_set::raise_cpi_nesting_limit_to_8::ID);svm=svm.with_compute_budget(ComputeBudget{compute_unit_limit:DIAGNOSTIC,heap_size:256*1024,..ComputeBudget::new_with_defaults(nesting)});}
        svm.airdrop(&payer.pubkey(),1_000_000_000).map_err(|e|anyhow!("airdrop: {e:?}"))?;svm.add_program(program,&elf).map_err(|e|anyhow!("load: {e:?}"))?;
        for (key,data) in [(proof_key,proof_data.to_vec()),(public_key,public.clone()),(checkpoint_key,checkpoint)]{svm.set_account(key,Account{lamports:100_000_000,data,owner:program,executable:false,rent_epoch:0})?;}
        let ix=Instruction{program_id:program,accounts:vec![AccountMeta::new_readonly(proof_key,false),AccountMeta::new_readonly(public_key,false),AccountMeta::new(checkpoint_key,false)],data};
        let instructions=[ComputeBudgetInstruction::set_compute_unit_limit(LIMIT),ComputeBudgetInstruction::request_heap_frame(256*1024),ix];
        let tx=Transaction::new_signed_with_payer(&instructions,Some(&payer.pubkey()),&[&payer],svm.latest_blockhash());
        let (error,meta)=match svm.send_transaction(tx){Ok(m)=>(None,m),Err(e)=>(Some(format!("{:?}",e.err)),e.meta)};
        ensure!(svm.get_account(&proof_key).unwrap().data==proof_data&&svm.get_account(&public_key).unwrap().data==public,"read-only inputs changed");
        let program_cu=meta.logs.iter().find_map(|l|l.strip_prefix(&format!("Program {program} consumed "))?.split_whitespace().next()?.parse::<u64>().ok());
        Ok(Run{error,cu:meta.compute_units_consumed,program_cu,logs:meta.logs,checkpoint:svm.get_account(&checkpoint_key).unwrap().data})
    };
    let send=|data:Vec<u8>,checkpoint:Vec<u8>,diagnostic:bool|->Result<Run> {send_with(&proof,data,checkpoint,diagnostic)};
    let record=|name:&str,run:&Run,diagnostic:bool|->Value {
        json!({"mode":name,"budget":if diagnostic {"DIAGNOSTIC elevated compute limit"}else{"acceptance at 1,400,000 CU"},"error":run.error,"transaction_cu":run.cu,"program_cu":run.program_cu,"phases":phases(&run.logs,if diagnostic {DIAGNOSTIC}else{LIMIT as u64}),"logs":run.logs})
    };
    let zero=vec![0u8;checkpoint_len];
    let mut runs=vec![];
    // Pinned pair, as deployed: each stage inside the real transaction limit.
    let tx1=send(vec![1,10],zero.clone(),false)?;ensure!(tx1.error.is_none(),"pinned stage 1 failed: {:?}",tx1.error);
    let tx2=send(vec![2],tx1.checkpoint.clone(),false)?;ensure!(tx2.error.is_none(),"pinned stage 2 failed: {:?}",tx2.error);
    runs.push(record("pinned-stage1",&tx1,false));runs.push(record("pinned-stage2",&tx2,false));
    let mut summary=json!({"pinned_stage1_cu":tx1.program_cu,"pinned_stage2_cu":tx2.program_cu,"pinned_sum_cu":tx1.program_cu.zip(tx2.program_cu).map(|(a,b)|a+b)});
    for (name,tag) in [("fused",8u8),("batched",9u8)] {
        let diagnostic=send(vec![tag],zero.clone(),true)?;ensure!(diagnostic.error.is_none(),"{name} diagnostic failed: {:?}",diagnostic.error);
        ensure!(diagnostic.checkpoint==zero,"{name} wrote the checkpoint account");
        let acceptance=send(vec![tag],zero.clone(),false)?;
        summary[format!("{name}_cu")]=json!(diagnostic.program_cu);
        summary[format!("{name}_completes_at_1400000")]=json!(acceptance.error.is_none());
        runs.push(record(&format!("{name}-diagnostic"),&diagnostic,true));runs.push(record(&format!("{name}-acceptance"),&acceptance,false));
        std::println!("{label} {name}: program CU {:?}; completes inside 1,400,000: {}",diagnostic.program_cu,acceptance.error.is_none());
    }
    // Cost probe for binding the opening inputs to one QM31 value (verifies nothing).
    let probe=send(vec![10],zero.clone(),false)?;ensure!(probe.error.is_none(),"input probe failed: {:?}",probe.error);
    summary["input_evaluation_probe_cu"]=json!(probe.program_cu);runs.push(record("input-evaluation-probe",&probe,false));
    // The summed format: the proof re-packed (one multiproof per tree, certificate inside).
    {
        #[derive(Clone,Copy)] struct Sha2;
        impl aspis_core::Digest32 for Sha2 { fn digest(&self,parts:&[&[u8]])->[u8;32]{let mut d=Sha256::new();for p in parts {d.update(p);}d.finalize().into()} }
        let statement=aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public).map_err(|e|anyhow!("statement: {e:?}"))?;
        let packed=aspis_r1_cost_probe::verifier::candidate::one_tx::pack(statement.semantic_public(),&proof,Sha2).map_err(|e|anyhow!("re-pack: {e:?}"))?;
        let diagnostic=send_with(&packed,vec![14],zero.clone(),true)?;
        if diagnostic.error.is_none() {
            let acceptance=send_with(&packed,vec![14],zero.clone(),false)?;
            let mut bad=packed.clone();let last=bad.len()-5;bad[last]^=1;
            let rejected=send_with(&bad,vec![14],zero.clone(),true)?;ensure!(rejected.error.is_some(),"summed format accepted a changed certificate byte");
            let pinned=send_with(&proof,vec![14],zero.clone(),true)?;ensure!(pinned.error.is_some(),"summed format accepted a pinned-format proof");
            summary["summed_format_cu"]=json!(diagnostic.program_cu);
            summary["summed_format_completes_at_1400000"]=json!(acceptance.error.is_none());
            summary["summed_format_proof_bytes"]=json!(packed.len());
            summary["summed_format_proof_sha256"]=json!(sha(&packed));
            runs.push(record("summed-format-diagnostic",&diagnostic,true));runs.push(record("summed-format-acceptance",&acceptance,false));
            std::println!("{label} summed format: program CU {:?}; completes inside 1,400,000: {}; proof bytes {}",diagnostic.program_cu,acceptance.error.is_none(),packed.len());
        } else {
            summary["summed_format_cu"]=json!(null);runs.push(record("summed-format-diagnostic",&diagnostic,true));
        }
    }
    // Stage D: the honest certificate is a function of the public proof data; it is
    // computed here on the host and placed at the start of the third account.
    {
        #[derive(Clone,Copy)] struct Sha;
        impl aspis_core::Digest32 for Sha { fn digest(&self,parts:&[&[u8]])->[u8;32]{let mut d=Sha256::new();for p in parts {d.update(p);}d.finalize().into()} }
        let statement=aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public).map_err(|e|anyhow!("statement: {e:?}"))?;
        let certificate=aspis_r1_cost_probe::verifier::candidate::one_tx::final_message_certificate(statement.semantic_public(),&proof,Sha).map_err(|e|anyhow!("certificate: {e:?}"))?;
        // Kept beside the record so the trace driver can replay the same run.
        fs::write(out.with_extension("cert"),&certificate)?;
        let mut account=zero.clone();account[..certificate.len()].copy_from_slice(&certificate);
        let diagnostic=send(vec![13],account.clone(),true)?;
        if diagnostic.error.is_none() {
            ensure!(diagnostic.checkpoint==account,"summed wrote the certificate account");
            let acceptance=send(vec![13],account.clone(),false)?;
            // Negative control on chain: one flipped certificate byte must be rejected.
            let mut bad=account.clone();bad[100]^=1;
            let rejected=send(vec![13],bad,true)?;ensure!(rejected.error.is_some(),"summed accepted a changed certificate");
            summary["summed_cu"]=json!(diagnostic.program_cu);
            summary["summed_completes_at_1400000"]=json!(acceptance.error.is_none());
            summary["summed_acceptance_cu"]=json!(if acceptance.error.is_none() {acceptance.program_cu} else {None});
            summary["certificate_sha256"]=json!(sha(&certificate));
            runs.push(record("summed-diagnostic",&diagnostic,true));runs.push(record("summed-acceptance",&acceptance,false));
            std::println!("{label} summed: program CU {:?}; completes inside 1,400,000: {}",diagnostic.program_cu,acceptance.error.is_none());
        } else {
            summary["summed_cu"]=json!(null);runs.push(record("summed-diagnostic",&diagnostic,true));
        }
    }
    // Unit-cost and relation-phase probes (the second exists in detail-phases builds only).
    for (name,tag) in [("unit-cost-probe",11u8),("relation-probe",12u8)] {
        let run=send(vec![tag],zero.clone(),false)?;
        summary[format!("{}_cu",name.replace('-',"_"))]=json!(if run.error.is_none() {run.program_cu} else {None});
        runs.push(record(name,&run,false));
    }
    std::println!("{label} pinned: stage 1 {:?}, stage 2 {:?}; input probe {:?}",tx1.program_cu,tx2.program_cu,probe.program_cu);
    let value=json!({"label":"FUTURE-VERSION EXPERIMENT — UNPROVED, local LiteSVM, verifier core without the Pool adapter","fixture":label,"source_revision":env::var("ASPIS_SOURCE_REVISION")?,"elf_sha256":sha(&elf),"proof_sha256":sha(&proof),"public_sha256":sha(&public),"runtime":{"litesvm":"0.16.0","agave":"4.2.1","heap_bytes":262144},"summary":summary,"runs":runs});
    fs::write(out,serde_json::to_string_pretty(&value)?+"\n")?;Ok(())
}
