use std::{env, fs, path::Path, str::FromStr};
use aspis_core::field::M31;
use aspis_pool::*;
use aspis_registry::*;
use aspis_statement::{derive_owner_key, encode_digest_canonical, pool_v1::*};
use base64::{engine::general_purpose::STANDARD as B64, Engine};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use solana_program::{instruction::{Instruction, AccountMeta}, pubkey::Pubkey};
#[path="../../live_context.rs"] mod live_context;
fn dig(s:u32)->[M31;8]{std::array::from_fn(|i|M31(s+17*i as u32+1))}
fn pk(v:&Value,n:&str)->Pubkey{Pubkey::from_str(v[n].as_str().unwrap()).unwrap()}
fn ro(p:Pubkey)->AccountMeta{AccountMeta::new_readonly(p,false)}
fn rw(p:Pubkey)->AccountMeta{AccountMeta::new(p,false)}
fn signer(p:Pubkey,w:bool)->AccountMeta{if w{AccountMeta::new(p,true)}else{AccountMeta::new_readonly(p,true)}}
fn ix(program:Pubkey,accounts:Vec<AccountMeta>,data:Vec<u8>)->Value{
    let i=Instruction{program_id:program,accounts,data};
    json!({"program":i.program_id.to_string(),"accounts":i.accounts.iter().map(|a|json!({"key":a.pubkey.to_string(),"signer":a.is_signer,"writable":a.is_writable})).collect::<Vec<_>>(),"data":B64.encode(i.data)})
}
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn bytes32(s:&str)->[u8;32]{assert_eq!(s.len(),64);std::array::from_fn(|i|u8::from_str_radix(&s[2*i..2*i+2],16).unwrap())}
fn account(v:&Value,key:Pubkey,owner:Pubkey)->Vec<u8>{let a=&v[&key.to_string()];assert_eq!(a["owner"],owner.to_string());assert_eq!(a["executable"],false);B64.decode(a["data"][0].as_str().unwrap()).unwrap()}
fn main(){
    let args:Vec<String>=env::args().collect();
    let cfg:Value=serde_json::from_slice(&fs::read(&args[2]).unwrap()).unwrap();
    let ids=&cfg["programs_and_accounts"];
    let pool=pk(ids,"pool");let registry=pk(ids,"registry");let verifier=pk(ids,"verifier");
    let payer=pk(ids,"payer");let authority=pk(ids,"authority");let mint=pk(ids,"mint");
    let system=Pubkey::default();let token=LEGACY_SPL_TOKEN_PROGRAM_ID;
    let master=pool_v1_pair_forest_master_address(&pool,&mint).0;
    let lanes:Vec<Pubkey>=(0..8).map(|i|pool_v1_pair_forest_lane_address(&pool,&master,i).unwrap().0).collect();
    let pages:Vec<Pubkey>=(0..8).map(|i|pool_v1_pair_forest_lane_root_page_address(&pool,&master,i,0).unwrap().0).collect();
    let checkpoint=pool_v1_pair_forest_checkpoint_address(&pool,&master,0).0;
    let vault=pool_v1_vault_token_account_address(&pool,&master).0;
    let reg=pool_v1_verifier_registry_v2_address(&registry,&master).0;
    let entry=pool_v1_verifier_entry_v2_address(&registry,&master,&V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,&V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING).0;
    let nullifier=pool_v1_nullifier(&dig(10),&dig(100));
    let output_lane=pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap() as usize;
    let marker=pool_v1_nullifier_marker_address(&pool,&master,&encode_digest_canonical(&nullifier)).unwrap().0;
    let init=PoolInitializationV1 {asset_mint:mint.to_bytes(),token_program:token.to_bytes(),asset_id:M31(77),deployment_domain:[5;32],verifier_policy:VerifierPolicyV1{flags:POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY|POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,registry_program:registry.to_bytes(),registry_authority:[0;32],policy_binding:[7;32]}};
    // Fixed note sequence, deposited in order until the selected output lane has a current page.
    // This is account provisioning, before any proof/transcript exists; no proof seed search.
    let mut trees:Vec<IncrementalMerkleTreeV1>=(0..8).map(|_|IncrementalMerkleTreeV1::from_parts_with_empty_roots(0,POOL_V1_PAIR_EMPTY_ROOTS[20],std::array::from_fn(|i|POOL_V1_PAIR_EMPTY_ROOTS[i]),&POOL_V1_PAIR_EMPTY_ROOTS).unwrap()).collect();
    let mut leaves:Vec<Vec<[M31;8]>>=vec![vec![];8];let mut deposits=vec![];let mut input_lane=0;
    for n in 0..32u32 {
        let req=aspis_pool::DepositRequestV1{owner_key:derive_owner_key(&dig(10)),salt:dig(100+100*n),amount:1000,encrypted_note_payload:&[]};
        let commitment=pool_v1_note_commitment(&req.owner_key,req.amount,M31(77),&req.salt);
        let lane=pool_v1_pair_forest_deposit_lane_v1(&commitment).unwrap() as usize;
        if n==0{input_lane=lane;}
        let mut metas=vec![ro(master),rw(lanes[lane]),rw(pages[lane]),ro(mint),rw(pk(ids,"source")),signer(pk(ids,"source_authority"),false),rw(vault),ro(token)];
        if trees[lane].next_leaf_index==0{metas.extend([signer(payer,true),ro(system)]);}
        let leaf=PoolV1PairLeafWitnessV1::single_output(commitment).unwrap().leaf_digest().unwrap();leaves[lane].push(leaf);
        trees[lane]=trees[lane].append_one_with_empty_roots(leaf,&POOL_V1_PAIR_EMPTY_ROOTS).unwrap().0;
        deposits.push(json!({"name":format!("deposit-{n}"),"lane":lane,"instruction":ix(pool,metas,encode_pair_forest_deposit_instruction_v1(&req).unwrap()),"expected_sequence":trees[lane].next_leaf_index}));
        if trees[output_lane].next_leaf_index>0{break;}
    }
    assert!(trees.iter().all(|t|t.next_leaf_index>0));
    match args[1].as_str(){
        "case-terminal"=>{
            let out=Path::new(&args[3]);
            let public=decode_pool_v1_private_transfer_public_v1(&fs::read(out.join("public.bin")).unwrap()).unwrap();
            let transition=decode_pool_v1_pair_late_public_statement_v1(&fs::read(out.join("transition.bin")).unwrap()).unwrap();
            let statement=decode_pool_v1_pair_forest_terminal_statement_v1(&fs::read(out.join("statement.bin")).unwrap()).unwrap();
            assert_eq!(statement.common().lane_transition,transition);
            assert_eq!(public.pool,master.to_bytes());
            let PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:bound,..}=statement else{panic!("transfer only")};assert_eq!(public,bound);
            let request=PoolV1PairForestTerminalRequestV1{verifier_profile:V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,verifier_release:V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,pool_program:pool.to_bytes(),public:PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)};
            let metas=vec![ro(master),ro(checkpoint),rw(lanes[output_lane]),rw(pages[output_lane]),rw(marker),signer(payer,true),ro(system),ro(reg),ro(entry),ro(verifier),ro(pk(ids,"proof"))];
            fs::write(out.join("terminal.json"),ix(pool,metas,encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap().to_vec()).to_string()).unwrap();
            fs::write(out.join("candidate.bin"),encode_pool_v1_pair_verified_afterstate_v1(&transition.candidate_afterstate).unwrap()).unwrap();
            println!("case statement and candidate match the generated transcript binding");
        }

        "plan"=>{
            let mut metas=vec![rw(master)];metas.extend(lanes.iter().copied().map(rw));metas.extend([ro(mint),rw(vault),ro(token),signer(payer,true),ro(system)]);
            let initialize=ix(pool,metas,encode_pair_forest_initialize_instruction_v1(&init).unwrap().to_vec());
            let mut metas=vec![rw(master)];metas.extend(lanes.iter().copied().map(ro));metas.extend([rw(checkpoint),signer(payer,true),ro(system)]);
            let receipts:Vec<Pubkey>=lanes.iter().map(|l|Pubkey::find_program_address(&[b"aspis-v8-lane-validation",l.as_ref()],&pool).0).collect();
            let preparations:Vec<Value>=lanes.iter().enumerate().map(|(i,l)|ix(pool,vec![ro(master),ro(*l),rw(receipts[i]),signer(payer,true),ro(system)],vec![b'A',b'S',b'8',b'V',1,i as u8,0,0])).collect();
            assert_eq!(cfg["checkpoint_receipts"],true);
            metas.extend(receipts.iter().copied().map(ro));
            println!("{}",json!({"receipts":receipts.iter().map(ToString::to_string).collect::<Vec<_>>(),"checkpoint_preparations":preparations,"master":master.to_string(),"lanes":lanes.iter().map(ToString::to_string).collect::<Vec<_>>(),"pages":pages.iter().map(ToString::to_string).collect::<Vec<_>>(),"vault":vault.to_string(),"checkpoint":checkpoint.to_string(),"registry":reg.to_string(),"entry":entry.to_string(),"nullifier_marker":marker.to_string(),"output_lane":output_lane,"input_lane":input_lane,"deposit_count":deposits.len(),"initialize":initialize,"deposits":deposits,"checkpoint_instruction":ix(pool,metas,b"AS8K\x01\x08\x01\x00".to_vec())}));
        }
        "registry"=>{
            let hashes:Value=serde_json::from_slice(&fs::read(&args[3]).unwrap()).unwrap();
            let loader=Pubkey::from_str("BPFLoaderUpgradeab1e11111111111111111111111").unwrap();
            let rd=Pubkey::find_program_address(&[registry.as_ref()],&loader).0;let vd=Pubkey::find_program_address(&[verifier.as_ref()],&loader).0;
            let slot=args[4].parse::<u64>().unwrap();
            println!("{}",json!({
                "initialize":ix(registry,vec![rw(reg),signer(authority,false),signer(payer,true),ro(system),ro(registry),ro(rd)],encode_initialize_registry_v2(master.to_bytes(),[7;32],1,bytes32(hashes["registry"].as_str().unwrap())).to_vec()),
                "schedule":ix(registry,vec![rw(reg),rw(entry),signer(authority,false),signer(payer,true),ro(system),ro(verifier),ro(vd)],encode_schedule_profile_v2(0,verifier.to_bytes(),V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,POOL_V1_PAIR_FOREST_TERMINAL_VERSION,slot,bytes32(hashes["verifier"].as_str().unwrap())).to_vec()),
                "activate":ix(registry,vec![rw(reg),rw(entry),signer(authority,false)],encode_simple_mutation_v2(RegistryMutationOpcodeV1::Activate,1).unwrap().to_vec()),
                "freeze":ix(registry,vec![rw(reg),signer(authority,false)],encode_simple_mutation_v2(RegistryMutationOpcodeV1::Freeze,2).unwrap().to_vec())}));
        }
        "context"|"validate-setup"=>{
            let snap:Value=serde_json::from_slice(&fs::read(&args[3]).unwrap()).unwrap();let a=&snap["accounts"];
            let m=decode_pool_v1_pair_forest_master_v1(&account(a,master,pool)).unwrap();
            assert_eq!(m.identity.asset_mint,mint.to_bytes());assert_eq!(m.identity.pool,master.to_bytes());assert_eq!(m.verifier_policy,init.verifier_policy);assert_eq!(m.identity.deployment_domain,init.deployment_domain);assert_eq!(m.identity.asset_id,M31(77));
            let live:Vec<_>=lanes.iter().enumerate().map(|(i,k)|{let l=decode_pool_v1_pair_forest_lane_state_v1(&account(a,*k,pool),&POOL_V1_PAIR_EMPTY_ROOTS).unwrap();assert_eq!(l.master,master.to_bytes());assert_eq!(l.lane_id,i as u8);assert_eq!(l.tree,trees[i]);l}).collect();
            let cp=decode_pool_v1_pair_forest_checkpoint_v1(&account(a,checkpoint,pool)).unwrap();assert_eq!(cp.master,master.to_bytes());assert_eq!(cp.checkpoint_sequence,0);assert_eq!(cp.lane_sequences,std::array::from_fn(|i|live[i].tree.next_leaf_index));
            assert_eq!(cp.global_root,pool_v1_pair_forest_global_root_v1(&std::array::from_fn(|i|live[i].tree.root)));
            if args[1]=="validate-setup" {
                println!("{}",json!({"authoritative_slot":snap["slot"],"all_eight_lanes_match_thirteen_deposits":true,"canonical_checkpoint_matches_live_roots":true,"master_identity_and_policy_match":true}));
                return;
            }
            let rv=decode_verifier_registry_v2(&account(a,reg,registry)).unwrap();let ev=decode_verifier_registry_entry_v2(&account(a,entry,registry)).unwrap();assert!(rv.is_immutable()&&!rv.is_paused());assert_eq!(ev.status,VerifierEntryStatusV1::Active);assert_eq!(ev.verifier_program,verifier.to_bytes());assert_eq!(ev.profile_binding,V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING);assert_eq!(ev.release_binding,V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING);
            let hashes:Value=serde_json::from_slice(&fs::read(Path::new(&args[2]).parent().unwrap().join("elf-hashes.json")).unwrap()).unwrap();
            assert_eq!(rv.pool,master.to_bytes());assert_eq!(rv.registry_program,registry.to_bytes());assert_eq!(rv.authority,[0;32]);assert_eq!(rv.policy_binding,[7;32]);assert_eq!(rv.generation,3);
            assert_eq!(rv.executable_hash,bytes32(hashes["registry"].as_str().unwrap()));assert_eq!(ev.executable_hash,bytes32(hashes["verifier"].as_str().unwrap()));
            assert_eq!(ev.pool,master.to_bytes());assert_eq!(ev.policy_binding,[7;32]);assert_eq!(ev.expected_upgrade_authority,[0;32]);assert!(ev.is_active_at(snap["slot"].as_u64().unwrap()));

            let mut nodes=leaves[input_lane].clone();let mut membership=vec![];
            for level in 0..20{membership.extend(encode_digest_canonical(nodes.get(1).unwrap_or(&POOL_V1_PAIR_EMPTY_ROOTS[level])));if nodes.len()%2==1{nodes.push(POOL_V1_PAIR_EMPTY_ROOTS[level]);}nodes=nodes.chunks_exact(2).map(|p|pool_v1_tree_parent(&p[0],&p[1])).collect();}
            assert_eq!(nodes[0],trees[input_lane].root);
            let mut roots:Vec<_>=trees.iter().map(|t|t.root).collect();let mut index=input_lane;let mut dirs=vec![];
            for _ in 0..3{membership.extend(encode_digest_canonical(&roots[index^1]));dirs.push((index&1)as u8);roots=roots.chunks_exact(2).map(|p|pool_v1_tree_parent(&p[0],&p[1])).collect();index/=2;}
            membership.extend(dirs);assert_eq!(roots[0],cp.global_root);
            let tree=live[output_lane].tree;
            let snapshot=PoolV1PairLiveSnapshotV1{pool:master.to_bytes(),deployment_domain:m.identity.deployment_domain,sequence:tree.next_leaf_index,next_pair_index:tree.next_leaf_index,current_root:tree.root,frontier:tree.frontier};
            let p=PoolV1PrivateTransferPublicV1{pool:master.to_bytes(),deployment_domain:m.identity.deployment_domain,anchor_sequence:cp.checkpoint_sequence,anchor_root:cp.global_root,nullifier,asset_id:M31(77),recipient_commitment:pool_v1_note_commitment(&derive_owner_key(&dig(300)),600,M31(77),&dig(400)),change_commitment:pool_v1_note_commitment(&derive_owner_key(&dig(500)),400,M31(77),&dig(600))};
            let out=Path::new(&args[4]);fs::create_dir(out).unwrap();fs::write(out.join("membership.bin"),membership).unwrap();
            // Candidate is constructed with the canonical append implementation, then recompiled from the live witness below.
            let pair=PoolV1PairLeafWitnessV1::two_outputs(p.recipient_commitment,p.change_commitment).unwrap().leaf_digest().unwrap();
            let(next,_)=tree.append_one_with_empty_roots(pair,&POOL_V1_PAIR_EMPTY_ROOTS).unwrap();
            let candidate=PoolV1PairVerifiedAfterstateV1{next_pair_index:next.next_leaf_index,next_root:next.root,next_frontier:next.frontier};
            let transition=PoolV1PairLatePublicStatementV1{live_snapshot:snapshot,candidate_afterstate:candidate};
            let statement=PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:p,common:PoolV1PairForestTerminalCommonV1{master_account:master.to_bytes(),checkpoint_account:checkpoint.to_bytes(),selected_lane_account:lanes[output_lane].to_bytes(),output_lane:output_lane as u8,checkpoint_sequence:cp.checkpoint_sequence,historical_global_anchor:cp.global_root,lane_transition:transition}};
            let sb=encode_pool_v1_pair_forest_terminal_statement_v1(&statement).unwrap();fs::write(out.join("statement.bin"),sb).unwrap();fs::write(out.join("verifier.bin"),verifier.to_bytes()).unwrap();fs::write(out.join("proof-account.bin"),pk(ids,"proof").to_bytes()).unwrap();
            env::set_var("ASPIS_V8_LIVE_CONTEXT",out);let(pp,w,ss)=live_context::load();
            let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&pp,&w,PoolV1PaymentRelationContextV1{runtime_binding:PoolV1PaymentRuntimeBindingV1{pool:p.pool,deployment_domain:p.deployment_domain,anchor_sequence:p.anchor_sequence,anchor_root:p.anchor_root,asset_id:p.asset_id},spent_nullifiers:&[]},ss).unwrap();assert_eq!(compiled.public_statement,transition);
            let request=PoolV1PairForestTerminalRequestV1{verifier_profile:V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,verifier_release:V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,pool_program:pool.to_bytes(),public:PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)};
            let metas=vec![ro(master),ro(checkpoint),rw(lanes[output_lane]),rw(pages[output_lane]),rw(marker),signer(payer,true),ro(system),ro(reg),ro(entry),ro(verifier),ro(pk(ids,"proof"))];
            fs::write(out.join("terminal.json"),ix(pool,metas,encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap().to_vec()).to_string()).unwrap();
            fs::write(out.join("candidate.bin"),encode_pool_v1_pair_verified_afterstate_v1(&candidate).unwrap()).unwrap();
            fs::write(out.join("expected-lane.bin"),encode_pool_v1_pair_forest_lane_state_v1(&PoolV1PairForestLaneStateV1{tree:next,..live[output_lane]},&POOL_V1_PAIR_EMPTY_ROOTS).unwrap()).unwrap();
            let result=PoolV1PairForestTerminalResultV1{transition_kind:statement.transition_kind(),master_account:master.to_bytes(),selected_lane_account:lanes[output_lane].to_bytes(),output_lane:output_lane as u8,nullifier,verified_afterstate:candidate};
            fs::write(out.join("expected-result.bin"),encode_pool_v1_pair_forest_terminal_result_v1(&result).unwrap()).unwrap();
            let mut history=RootHistoryPageV1::decode(&account(a,pages[output_lane],pool)).unwrap();
            assert_eq!(history.pool,lanes[output_lane].to_bytes());assert_eq!(history.page_number,0);assert_eq!(history.get(tree.next_leaf_index),Some(&tree.root));
            history.push(next.next_leaf_index,next.root).unwrap();fs::write(out.join("expected-history.bin"),history.encode().unwrap()).unwrap();
            let marker_payload=PoolV1NullifierMarkerV1{transition_kind:statement.transition_kind(),pool:master.to_bytes(),deployment_domain:p.deployment_domain,nullifier,retained_anchor_sequence:p.anchor_sequence,retained_anchor_root:p.anchor_root,verifier_profile:V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,verifier_release:V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING};
            assert!(a[&marker.to_string()].is_null());fs::write(out.join("expected-marker.bin"),encode_pool_v1_nullifier_marker(&marker_payload).unwrap()).unwrap();

            println!("{}",json!({"statement_sha256":hash(&sb),"input_value":1000,"recipient_value":600,"change_value":400,"input_lane":input_lane,"output_lane":output_lane,"before_sequence":tree.next_leaf_index,"after_sequence":next.next_leaf_index,"live_snapshot_slot":snap["slot"],"compiler_matches_authoritative_transition":true}));
        }
        _=>panic!("plan|registry|context"),
    }
}
