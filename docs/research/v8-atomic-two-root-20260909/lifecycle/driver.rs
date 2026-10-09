//! Actual local account creation/upload/seal/settlement/refund. No network keys.
use super::*;
fn convert(i:solana_program::instruction::Instruction)->Instruction{
 Instruction{program_id:address(&i.program_id),accounts:i.accounts.iter().map(|a|solana_instruction::AccountMeta{pubkey:address(&a.pubkey),is_signer:a.is_signer,is_writable:a.is_writable}).collect(),data:i.data}
}
fn life(data:Vec<u8>,authority:LegacyPubkey,proof_signs:bool)->Instruction{
 Instruction{program_id:address(&LegacyPubkey::from_str(VERIFIER_PROGRAM_ID).unwrap()),accounts:vec![
  if proof_signs{signer_meta(legacy(PROOF_ACCOUNT_BYTES),true)}else{meta(legacy(PROOF_ACCOUNT_BYTES),true)},
  signer_meta(authority,true)],data}
}
fn chunk(offset:usize,bytes:&[u8])->Vec<u8>{
 let mut d=vec![1];d.extend((offset as u32).to_le_bytes());d.extend((bytes.len() as u32).to_le_bytes());d.extend(bytes);d
}
fn inventory(svm:&LiteSVM,keys:&[LegacyPubkey])->serde_json::Value{
 serde_json::json!(keys.iter().map(|k|{
  let a=svm.get_account(&address(k));
  serde_json::json!({"key":k.to_string(),"state":a.map(|a|serde_json::json!({"owner":a.owner.to_string(),"lamports":a.lamports,"executable":a.executable,"bytes":a.data.len(),"sha256":sha256_hex(&a.data)}))})
 }).collect::<Vec<_>>())
}
fn execute(svm:&mut LiteSVM,payer:&Keypair,extra:&[&Keypair],ixs:&[Instruction],name:&str,success:bool,keys:&[LegacyPubkey])->Result<serde_json::Value>{
 svm.expire_blockhash();let before=snapshot(svm,keys);let manifest_before=inventory(svm,keys);
 let config=TransactionConfig::empty().with_priority_fee(10000).with_compute_unit_limit(1200000).with_loaded_accounts_data_size_limit(8388608).with_heap_size(262144);
 let msg=v1::Message::try_compile_with_config(&payer.pubkey(),ixs,svm.latest_blockhash(),config)?;
 let mut signers=vec![payer];signers.extend_from_slice(extra);
 let tx=VersionedTransaction::try_new(VersionedMessage::V1(msg),&signers)?;
 let wire=wincode::serialize(&tx)?;let sigs=tx.signatures.iter().map(|s|s.to_string()).collect::<Vec<_>>();
 ensure!(wire.len()<=4096 && wire[0]==0x81 && u32::from_le_bytes(wire[4..8].try_into().unwrap())==31);
 let n=wire[41] as usize;let p=42+32*n;
 ensure!(n<=64 && wire[40]<=64 && u64::from_le_bytes(wire[p..p+8].try_into().unwrap())==10000);
 ensure!(u32::from_le_bytes(wire[p+8..p+12].try_into().unwrap())==1200000);
 ensure!(u32::from_le_bytes(wire[p+12..p+16].try_into().unwrap())==8388608);
 ensure!(u32::from_le_bytes(wire[p+16..p+20].try_into().unwrap())==262144);
 let balance=svm.get_account(&payer.pubkey()).unwrap().lamports;
 let sim=svm.simulate_transaction(tx.clone());let sent=svm.send_transaction(tx);
 let (m,error)=match sent{
  Ok(m)=>{ensure!(success,"{name}: unexpected acceptance");ensure!(sim.unwrap().meta==m);(m,None)},
  Err(e)=>{ensure!(!success,"{name}: {:?}\n{}",e.err,e.meta.pretty_logs());let s=sim.unwrap_err();ensure!(s.err==e.err&&s.meta==e.meta);(e.meta,Some(format!("{:?}",e.err)))}
 };
 ensure!(m.compute_units_consumed<=1200000);
 if !success{ensure!(snapshot(svm,keys)==before,"{name}: failure did not roll back")}
 let app:Vec<_>=keys.iter().copied().filter(|k|k.to_bytes()!=PROOF_ACCOUNT_BYTES).collect();
 for k in &app{let i=keys.iter().position(|x|x==k).unwrap();ensure!(svm.get_account(&address(k))==before[i],"{name}: lifecycle changed application/context state")}
 let delta=balance as i64-svm.get_account(&payer.pubkey()).unwrap().lamports as i64;
 println!("LIFECYCLE_CASE {name} accepted={success} cu={} bytes={} payer_delta={delta}",m.compute_units_consumed,wire.len());
 Ok(serde_json::json!({"name":name,"accepted":success,"error":error,"cu":m.compute_units_consumed,"signed_transaction_bytes":wire.len(),"signed_transaction_hex":bytes_hex(&wire),"signed_transaction_sha256":sha256_hex(&wire),"signatures":sigs,"signature_count":signers.len(),"configured_cu":1200000,"heap_bytes":262144,"loaded_data_limit":8388608,"payer_lamport_decrease":delta,"ordinary_fee":5000*signers.len()+10000,"logs":m.logs,"application_context_unchanged":true,"protected_before":manifest_before,"protected_after":inventory(svm,keys),"instructions":ixs.iter().map(|i|serde_json::json!({"program":i.program_id.to_string(),"data_hex":bytes_hex(&i.data),"accounts":i.accounts.iter().map(|a|serde_json::json!({"key":a.pubkey.to_string(),"signer":a.is_signer,"writable":a.is_writable})).collect::<Vec<_>>()})).collect::<Vec<_>>()}))
}
pub(super) fn run(svm:&mut LiteSVM,payer:&Keypair,args:&Args,keys:&[LegacyPubkey],original:Instruction,lane:&PoolV1PairForestLaneStateV1,afterstate:&PoolV1PairVerifiedAfterstateV1,request:&PoolV1PairForestTerminalRequestV1,expected:&[u8])->Result<()>{
 let proof=Keypair::new_from_array([3u8;32]);let other=Keypair::new_from_array([2u8;32]);
 ensure!(proof.pubkey().to_bytes()==PROOF_ACCOUNT_BYTES && svm.get_account(&proof.pubkey()).is_none());
 ensure!(expected.len()==41010 && expected[..4]==*b"ASPU" && expected[8..40]==[0u8;32]);
 let verifier=LegacyPubkey::from_str(VERIFIER_PROGRAM_ID)?;let authority=legacy(payer.pubkey().to_bytes());let pkey=legacy(PROOF_ACCOUNT_BYTES);
 let rent=solana_program::rent::Rent::default().minimum_balance(expected.len());
 let create=convert(solana_program::system_instruction::create_account(&authority,&pkey,rent,expected.len() as u64,&verifier));
 let mut init=vec![0];init.extend(((expected.len()-40) as u32).to_le_bytes());
 let init_ix=life(init.clone(),authority,true);
 let mut normal=vec![];let mut negative=vec![];
 normal.push(execute(svm,payer,&[&proof],&[create.clone(),init_ix.clone()],"create-and-init",true,keys)?);
 let created=svm.clone();
 for (name,ix,extra) in [
  ("wrong-upload-authority",life(chunk(0,&[1]),legacy(other.pubkey().to_bytes()),false),vec![&other]),
  ("upload-overflow",life(chunk(u32::MAX as usize,&[1]),authority,false),vec![]),
  ("upload-length-mismatch",life({let mut d=chunk(0,&[1]);d.push(2);d},authority,false),vec![]),
  ("unrelated-tag",life(vec![63],authority,false),vec![]),
  ("close-unsealed",life(vec![64],authority,true),vec![&proof]),
  ("noncanonical-init-size",life(vec![0,176,2,0,0],authority,true),vec![&proof]),
 ]{negative.push(execute(&mut svm.clone(),payer,&extra,&[ix],name,false,keys)?);}
 let mut unsigned=life(chunk(0,&[1]),authority,false);unsigned.accounts[1].is_signer=false;
 // The payer is necessarily a transaction signer; use the existing second
 // funded authority as an actually unsigned authority-role account.
 unsigned.accounts[1].pubkey=other.pubkey();
 negative.push(execute(&mut svm.clone(),payer,&[],&[unsigned],"unsigned-upload-authority",false,keys)?);
 let mut unsigned_init=created.clone();
 negative.push(execute(&mut unsigned_init,payer,&[],&[original.clone()],"unsealed-source-verification",false,keys)?);
 let mut hole=None;
 for (i,bytes) in expected[40..].chunks(3500).enumerate(){
  if (i+1)*3500>=expected.len()-40 {hole=Some(svm.clone());}
  normal.push(execute(svm,payer,&[],&[life(chunk(i*3500,bytes),authority,false)],&format!("upload-{i:02}"),true,keys)?);
 }
 let mut incomplete=hole.unwrap();
 negative.push(execute(&mut incomplete,payer,&[],&[life(vec![62],authority,false)],"diagnostic-seal-incomplete",true,keys)?);
 negative.push(execute(&mut incomplete,payer,&[],&[original.clone()],"incomplete-source-verification",false,keys)?);
 normal.push(execute(svm,payer,&[],&[life(vec![62],authority,false)],"seal",true,keys)?);
 ensure!(svm.get_account(&proof.pubkey()).unwrap().data==expected,"actual uploaded/sealed bytes differ from expected account");
 for (name,ix) in [
  ("write-after-seal",life(chunk(0,&[1]),authority,false)),
  ("seal-twice",life(vec![62],authority,false)),
  ("reinitialize-sealed",life(init.clone(),authority,false)),
  ("close-without-proof-signature",life(vec![64],authority,false)),
  ("seal-trailing-data",life(vec![62,0],authority,false)),
 ]{negative.push(execute(&mut svm.clone(),payer,&[],&[ix],name,false,keys)?);}
 // Exact retained maximum proof at this different, genuinely signed address
 // must reject. Upload it through the SAME real lifecycle, not set_account.
 let ex=PathBuf::from(env::var("ASPIS_LIFECYCLE")?);let old=fs::read(ex.join("../../../../fixtures/transfer-255-1.bin"))?;
 ensure!(old.len()==40282 && sha256_hex(&old)=="4cbeb8a7a5110f2bd5b8086b57d36408a30afe1a923dbe625763eeaf1338b6d9");
 let mut substituted=created.clone();let mut wrong=expected[40..728].to_vec();wrong.extend(old);
 for (i,bytes) in wrong.chunks(3500).enumerate(){negative.push(execute(&mut substituted,payer,&[],&[life(chunk(i*3500,bytes),authority,false)],&format!("diagnostic-old-proof-upload-{i:02}"),true,keys)?);}
 negative.push(execute(&mut substituted,payer,&[],&[life(vec![62],authority,false)],"diagnostic-old-proof-seal",true,keys)?);
 negative.push(execute(&mut substituted,payer,&[],&[original.clone()],"old-proof-at-new-address",false,keys)?);
 // Existing real-verifier success and all rollback/adversarial controls now
 // start from an account created, uploaded and sealed by signed transactions.
 atomic::run(svm,payer,args,keys,original.clone(),lane,afterstate,request)?;
 let mut evidence:serde_json::Value=serde_json::from_slice(&fs::read(&args.evidence)?)?;
 let b=LegacyPubkey::from_str(evidence["cases"][0]["instructions"][0]["accounts"].as_array().unwrap().iter().rev().nth(1).unwrap()["key"].as_str().unwrap())?;
 let mut settled_keys=keys.to_vec();settled_keys.push(b);
 let close=life(vec![64],authority,true);
 let credit=convert(solana_program::system_instruction::transfer(&authority,&pkey,1));
 negative.push(execute(&mut svm.clone(),payer,&[&proof],&[close.clone(),credit,life(vec![62],authority,false)],"close-credit-reseal-rollback",false,&settled_keys)?);
 let refundable=svm.get_account(&proof.pubkey()).unwrap().lamports;
 normal.push(execute(svm,payer,&[&proof],&[close.clone()],"cleanup-refund",true,&settled_keys)?);
 ensure!(svm.get_account(&proof.pubkey()).is_none());
 ensure!(normal.last().unwrap()["payer_lamport_decrease"].as_i64()==Some(20000-refundable as i64));
 // Recreating storage is authorized by its retained key, but never resets
 // the Pool's consumed nullifier or either application's settled root.
 let mut replay=svm.clone();
 negative.push(execute(&mut replay,payer,&[&proof],&[create,init_ix],"diagnostic-recreate-storage",true,&settled_keys)?);
 for (i,bytes) in expected[40..].chunks(3500).enumerate(){negative.push(execute(&mut replay,payer,&[],&[life(chunk(i*3500,bytes),authority,false)],&format!("diagnostic-recreate-upload-{i:02}"),true,&settled_keys)?);}
 negative.push(execute(&mut replay,payer,&[],&[life(vec![62],authority,false)],"diagnostic-recreate-seal",true,&settled_keys)?);
 negative.push(execute(&mut replay,payer,&[],&[original],"recreated-proof-cannot-replay",false,&settled_keys)?);
 evidence["proof_upload"]="actual signed System create + init, 12 uploads and seal; no proof account set_account injection".into();
 evidence["lifecycle"]=serde_json::json!({"schema":"aspis.v8.atomic.lifecycle.v1","normal_transactions":normal,"diagnostic_transactions":negative,"proof_account":proof.pubkey().to_string(),"proof_key_retained":true,"refund_destination":payer.pubkey().to_string(),"refunded_lamports":refundable,"proof_account_absent_after_cleanup":true,"sealed_account_sha256":sha256_hex(expected),"source_and_destination_transition_only_in_settlement":true,"network_transactions":0,"local_commitment":"LiteSVM committed transaction; no cluster-finality claim"});
 fs::write(&args.evidence,serde_json::to_vec_pretty(&evidence)?)?;
 Ok(())
}
