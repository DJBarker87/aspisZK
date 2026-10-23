//! Native differential fixtures. Runtime-admitted entries have fresh cells/counter0.
use super::*;
use aspis_statement::pool_v1::*;
use std::{fmt::Debug, str::FromStr, sync::Mutex};
const POOL: [u8; 32] = [0x41; 32];
const REGISTRY: [u8; 32] = [0x44; 32];
const PROFILE: [u8; 32] = PROFILE_BINDING;
const RELEASE: [u8; 32] = RELEASE_BINDING;
const POOL_V1_PAIR_EMPTY_ROOTS: [[M31; 8]; POOL_V1_PAIR_TREE_DEPTH+1] = v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
macro_rules! ensure { ($cond:expr $(,$message:expr)?) => { if !$cond { return Err(format!("fixture guard: {}", stringify!($cond))); } }; }
fn checked<T, E: Debug>(r: Result<T, E>) -> Result<T, String> { r.map_err(|e| format!("{e:?}")) }
fn pool_v1_pair_forest_master_address(pool: &Pubkey, mint: &Pubkey) -> (Pubkey,u8) {
    Pubkey::find_program_address(&[PAIR_FOREST_MASTER_SEED,mint.as_ref()],pool)
}
fn pool_v1_pair_forest_lane_address(pool: &Pubkey, master: &Pubkey, lane:u8) -> Result<(Pubkey,u8),String> {
    Ok(Pubkey::find_program_address(&[PAIR_FOREST_LANE_SEED,master.as_ref(),&[lane]],pool))
}
fn pool_v1_pair_forest_checkpoint_address(pool: &Pubkey, master:&Pubkey, sequence:u64) -> (Pubkey,u8) {
    Pubkey::find_program_address(&[PAIR_FOREST_CHECKPOINT_SEED,master.as_ref(),&sequence.to_le_bytes()],pool)
}
fn pool_v1_verifier_registry_v2_address(registry: &Pubkey, master:&Pubkey) -> (Pubkey,u8) {
    Pubkey::find_program_address(&[VERIFIER_REGISTRY_V2_SEED,master.as_ref()],registry)
}
fn pool_v1_verifier_entry_v2_address(registry: &Pubkey, master:&Pubkey, profile:&[u8;32], release:&[u8;32]) -> (Pubkey,u8) {
    Pubkey::find_program_address(&[VERIFIER_ENTRY_V2_SEED,master.as_ref(),profile,release],registry)
}
#[derive(Clone)]
struct Image { name: &'static str, key: Pubkey, owner: Pubkey, data: Vec<u8> }
fn image(name: &'static str,key:Pubkey,owner:Pubkey,data:Vec<u8>) -> Image {Image{name,key,owner,data}}
fn images(program: Pubkey, proof: &[u8], public: &[u8]) -> Result<(Vec<Image>, Vec<u8>, Vec<u8>), String> {
    ensure!(
        proof.len() == 57607,
        "wrong frozen proof"
    );
    ensure!(
        public.len() == 1880,
        "wrong frozen ASF8"
    );
    let statement = checked(decode_pool_v1_pair_forest_terminal_statement_v1(public))?;
    ensure!(
        checked(encode_pool_v1_pair_forest_terminal_statement_v1(&statement))?.as_slice() == public
    );
    let c = *statement.common();
    let s = c.lane_transition.live_snapshot;
    ensure!(c.checkpoint_sequence == 42 && c.output_lane == 3);
    ensure!(s.sequence == s.next_pair_index);
    let payment = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public)
        }
    };
    let asset_id = match payment {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p) => p.asset_id,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(p) => p.asset_id,
    };
    let pool = Pubkey::new_from_array(POOL);
    let registry_program = Pubkey::new_from_array(REGISTRY);
    let mint = Pubkey::new_from_array([0x42; 32]);
    let (master_key, master_bump) = pool_v1_pair_forest_master_address(&pool, &mint);
    let (lane_key, lane_bump) = checked(pool_v1_pair_forest_lane_address(
        &pool,
        &master_key,
        c.output_lane,
    ))?;
    let (pool_checkpoint, checkpoint_bump) =
        pool_v1_pair_forest_checkpoint_address(&pool, &master_key, c.checkpoint_sequence);
    ensure!(
        master_key.to_bytes() == c.master_account
            && lane_key.to_bytes() == c.selected_lane_account
            && pool_checkpoint.to_bytes() == c.checkpoint_account
    );
    let master = PoolV1PairForestMasterV1 {
        bump: master_bump,
        identity: PoolIdentityV1 {
            pool: master_key.to_bytes(),
            asset_mint: mint.to_bytes(),
            token_program: Pubkey::from_str("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA").unwrap()
                .to_bytes(),
            asset_id,
            deployment_domain: s.deployment_domain,
        },
        verifier_policy: VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
                | POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
            registry_program: REGISTRY,
            registry_authority: [0; 32],
            policy_binding: [7; 32],
        },
        initialized_lane_mask: 0xff,
        has_checkpoint: true,
        next_checkpoint_sequence: 43,
        last_checkpoint_lane_sequences: [0; 8],
    };
    let checkpoint = PoolV1PairForestCheckpointV1 {
        bump: checkpoint_bump,
        master: master_key.to_bytes(),
        deployment_domain: s.deployment_domain,
        checkpoint_sequence: c.checkpoint_sequence,
        global_root: c.historical_global_anchor,
        lane_sequences: [0; 8],
    };
    let lane = PoolV1PairForestLaneStateV1 {
        bump: lane_bump,
        master: master_key.to_bytes(),
        lane_id: c.output_lane,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: s.next_pair_index,
            root: s.current_root,
            frontier: s.frontier,
        },
    };
    let loader = bpf_loader_upgradeable::id();
    let (registry_key, registry_bump) =
        pool_v1_verifier_registry_v2_address(&registry_program, &master_key);
    let (entry_key, entry_bump) =
        pool_v1_verifier_entry_v2_address(&registry_program, &master_key, &PROFILE, &RELEASE);
    let (registry_pd, registry_pd_bump) =
        Pubkey::find_program_address(&[registry_program.as_ref()], &loader);
    let (verifier_pd, verifier_pd_bump) =
        Pubkey::find_program_address(&[program.as_ref()], &loader);
    // Fixed nonzero measurement descriptors, intentionally NOT a certificate of
    // either loaded ELF. Their identical bytes must survive both executions.
    let registry = VerifierRegistryV2 {
        bump: registry_bump,
        programdata_bump: registry_pd_bump,
        flags: POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE,
        pool: master_key.to_bytes(),
        authority: [0; 32],
        policy_binding: [7; 32],
        generation: 1,
        minimum_activation_delay_slots: 1,
        registry_program: REGISTRY,
        loader_program: loader.to_bytes(),
        programdata_address: registry_pd.to_bytes(),
        executable_hash: [0xa5; 32],
    };
    let entry = VerifierRegistryEntryV2 {
        bump: entry_bump,
        programdata_bump: verifier_pd_bump,
        status: VerifierEntryStatusV1::Active,
        statement_version: POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
        pool: master_key.to_bytes(),
        verifier_program: program.to_bytes(),
        profile_binding: PROFILE,
        release_binding: RELEASE,
        loader_program: loader.to_bytes(),
        programdata_address: verifier_pd.to_bytes(),
        executable_hash: [0x5a; 32],
        expected_upgrade_authority: [0; 32],
        activation_slot: 0,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: [7; 32],
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: PROFILE,
        verifier_release: RELEASE,
        pool_program: POOL,
        public: payment,
    };
    // Reconstruct exactly what the adapter reads from the image carriers.
    let reconstructed = checked(reconstruct_pool_v1_pair_forest_terminal_statement_v1(
        &request,
        PoolV1PairForestTerminalCommonV1 {
            master_account: master.identity.pool,
            checkpoint_account: pool_checkpoint.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane.lane_id,
            checkpoint_sequence: checkpoint.checkpoint_sequence,
            historical_global_anchor: checkpoint.global_root,
            lane_transition: PoolV1PairLatePublicStatementV1 {
                live_snapshot: PoolV1PairLiveSnapshotV1 {
                    pool: master.identity.pool,
                    deployment_domain: master.identity.deployment_domain,
                    sequence: lane.tree.next_leaf_index,
                    next_pair_index: lane.tree.next_leaf_index,
                    current_root: lane.tree.root,
                    frontier: lane.tree.frontier,
                },
                candidate_afterstate: c.lane_transition.candidate_afterstate,
            },
        },
    ))?;
    ensure!(
        checked(encode_pool_v1_pair_forest_terminal_statement_v1(
            &reconstructed
        ))?
        .as_slice()
            == public,
        "image-derived ASF8 mismatch"
    );
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: c.master_account,
        selected_lane_account: c.selected_lane_account,
        output_lane: c.output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: c.lane_transition.candidate_afterstate,
    };
    checked(
        validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement, &result),
    )?;
    let mut proof_image = checked(encode_pool_v1_pair_verified_afterstate_v1(
        &c.lane_transition.candidate_afterstate,
    ))?
    .to_vec();
    ensure!(proof_image.len() == 688);
    proof_image.extend_from_slice(proof);
    let foreign = Pubkey::new_from_array([0x55; 32]);
    Ok((
        vec![
            image(
                "proof",
                Pubkey::new_from_array([0x45; 32]),
                foreign,
                proof_image,
            ),
            image(
                "public",
                Pubkey::new_from_array([0x46; 32]),
                foreign,
                public.to_vec(),
            ),
            image(
                "master",
                master_key,
                pool,
                checked(encode_pool_v1_pair_forest_master_v1(&master))?.to_vec(),
            ),
            image(
                "pool-checkpoint",
                pool_checkpoint,
                pool,
                checked(encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint))?.to_vec(),
            ),
            image(
                "lane",
                lane_key,
                pool,
                checked(encode_pool_v1_pair_forest_lane_state_v1(
                    &lane,
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                ))?
                .to_vec(),
            ),
            image(
                "registry",
                registry_key,
                registry_program,
                checked(encode_verifier_registry_v2(&registry))?.to_vec(),
            ),
            image(
                "entry",
                entry_key,
                registry_program,
                checked(encode_verifier_registry_entry_v2(&entry))?.to_vec(),
            ),
        ],
        checked(encode_pool_v1_pair_forest_terminal_request_v1(&request))?.to_vec(),
        checked(encode_pool_v1_pair_forest_terminal_result_v1(&result))?.to_vec(),
    ))
}

static RETURN: Mutex<Vec<u8>> = Mutex::new(Vec::new());
struct Stubs;
impl solana_program::program_stubs::SyscallStubs for Stubs {
    fn sol_log(&self, _: &str) {}
    fn sol_set_return_data(&self, bytes:&[u8]) { *RETURN.lock().unwrap() = bytes.to_vec(); }
    fn sol_get_clock_sysvar(&self, address:*mut u8) -> u64 {
        unsafe { std::ptr::write(address as *mut Clock, Clock{slot:150,..Clock::default()}); }
        0
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Record {key:Pubkey,owner:Pubkey,lamports:u64,data:Vec<u8>,signer:bool,writable:bool,executable:bool,rent:u64}
impl Record {
    fn from(i:&Image,writable:bool)-> Self {Self{key:i.key,owner:i.owner,lamports:1,data:i.data.clone(),signer:false,writable,executable:false,rent:0}}
    fn info(&mut self)->AccountInfo<'_> {AccountInfo::new(&self.key,self.signer,self.writable,&mut self.lamports,&mut self.data,&self.owner,self.executable,self.rent)}
}
fn run(old:bool, program:&Pubkey, mut records:Vec<Record>, data:&[u8], borrow_mode:usize) -> (ProgramResult, Vec<Record>, Vec<u8>) {
    *RETURN.lock().unwrap() = vec![0x72;3];
    let result = {
        let mut accounts:Vec<_> = records.iter_mut().map(Record::info).collect();
        // SDK duplicate deserialization clones the first complete AccountInfo.
        // Do the same, rather than manufacturing equal keys with fresh cells.
        for i in 0..accounts.len() {
            for j in 0..i {
                if accounts[i].key == accounts[j].key { accounts[i]=accounts[j].clone(); break; }
            }
        }
        // Only counter0 is runtime admission. Nonzero counters below are
        // separately reported diagnostics; guards are retained and then dropped.
        let held = if borrow_mode == 1 { Some(accounts[0].try_borrow_data().unwrap()) } else {None};
        let result = if old {crate::r1_pool_adapter_original::process(program,&accounts,data)} else {process(program,&accounts,data)};
        drop(held);
        for a in &accounts { assert!(a.data.try_borrow_mut().is_ok(),"leaked guard"); }
        result
    };
    (result,records,RETURN.lock().unwrap().clone())
}
fn compare(program:&Pubkey, records:Vec<Record>, data:&[u8], label:&str) -> (ProgramResult, Vec<Record>, Vec<u8>) {
    let old=run(true,program,records.clone(),data,0);
    let new=run(false,program,records,data,0);
    assert_eq!(old,new,"differential mismatch: {label}");
    new
}
#[test]
fn owned_adapter_native_differential_six_fixtures_and_1200_mutations() {
    let old_stubs=solana_program::program_stubs::set_syscall_stubs(Box::new(Stubs));
    let program=Pubkey::from_str("7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue").unwrap();
    let base=std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures");
    let mut mutations=0;
    let mut unique=0;
    for kind in ["transfer","withdrawal"] {for count in [13,255,1023] {
        let name=format!("{kind}-{count}");
        let proof=std::fs::read(base.join(&name).join("r1-s2-proof.bin")).unwrap();
        let public=std::fs::read(base.join(&name).join("r1-s2-public-asf8.bin")).unwrap();
        let (imgs,request,expected)=images(program,&proof,&public).unwrap();
        let cp=Image{name:"verifier-checkpoint",key:Pubkey::new_from_array([0x68;32]),owner:program,data:vec![0;1768]};
        let stage1=vec![Record::from(&imgs[0],false),Record::from(&imgs[1],false),Record::from(&cp,true)];
        let (result,saved,returned)=compare(&program,stage1.clone(),&[3,10],&name);
        assert_eq!(result,Ok(()));assert_eq!(returned,vec![0x72;3]);
        compare(&program,stage1.clone(),&[3,11],&format!("{name}-split11"));
        let mut stage2:Vec<_>=[0,2,3,4,5,6].iter().map(|i|Record::from(&imgs[*i],false)).collect();
        let mut saved_cp=saved[2].clone();saved_cp.writable=false;stage2.push(saved_cp);
        let (result,_,returned)=compare(&program,stage2.clone(),&request,&name);
        assert_eq!(result,Ok(()));assert_eq!(returned,expected);
        for stage in [1,2] { let mut seen=std::collections::HashSet::new(); for mutation in 0..100 {
            let mut records=if stage==1 {stage1.clone()} else {stage2.clone()};
            let mut data=if stage==1 {vec![3,10]} else {request.clone()};
            let index=(mutation/10)%records.len();
            match mutation%10 {
                0=>{ records[index].data.truncate(mutation); },
                1=>{ records[index].data.push(0); },
                2=>{ let width=records[index].data.len();if width>0 {records[index].data[(mutation*17)%width]^=1;} },
                3=>records[index].signer=true,
                4=>records[index].writable=!records[index].writable,
                5=>records[index].executable=true,
                6=>records[index].owner=Pubkey::new_from_array([0x79;32]),
                7=>{let other=(index+1)%records.len();records[index].key=records[other].key;},
                8=>{let width=data.len();data[mutation%width]^=1;},
                _=>{ records.pop(); },
            }
            if records[0].data.len()>8192 { records[0].data[4096+mutation*31] ^= 0x40; }
            if seen.insert((records.clone(),data.clone())) {unique+=1;}
            compare(&program,records,&data,&format!("{name}-s{stage}-m{mutation}"));mutations+=1;
        }}
        // Out-of-runtime-domain shared counter1 diagnostic, no equivalence claim.
        let old=run(true,&program,stage1.clone(),&[3,10],1);
        let new=run(false,&program,stage1,&[3,10],1);
        println!("counter1 diagnostic {name}: old={:?} new={:?}",old.0,new.0);
        println!("NATIVE fixture={name} both_stages=true errors_equal=true outputs_equal=true frames_equal=true");
    }}
    assert_eq!(mutations,1200);
    assert!(unique>=1000,"unique mutated inputs={unique}");
    println!("NATIVE runtime_admitted_mutations={mutations}; distinct_mutated_inputs={unique}; counter0 checked at every entry; nonzero diagnostics=6");
    solana_program::program_stubs::set_syscall_stubs(old_stubs);
}
