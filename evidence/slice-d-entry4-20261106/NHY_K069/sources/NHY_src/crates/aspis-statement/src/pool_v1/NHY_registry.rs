//! Exact private fixed32 zero-binding leaf.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn binding_ref(value:&[u8;32])->bool{*value==[0u8;32]}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn binding_packet(value:&[u8;32])->bool{required_binding_is_zero(value)==binding_ref(value)}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn binding_wrong_packet(value:&[u8;32])->bool{required_binding_is_zero(value)!=binding_ref(value)}
#[kani::proof_for_contract(binding_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn binding(){binding_packet(&kani::any());}
#[kani::proof_for_contract(binding_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn binding_wrong(){binding_wrong_packet(&kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_array_packet(bytes:&[u8;256],p:usize,j:usize)->bool{
 kani::assume(p<=224);kani::assume(j<32);
 let start=core::cmp::min(p,192);
 let rel=p-start;
 let window=&bytes[start..start+64];
 let actual=&bytes[p..p+32];
 let local=&window[rel..rel+32];
 (rel<=32 && actual.len()==32 && window.len()==64 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(registry_array_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_array(){registry_array_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_array_wrong_packet(bytes:&[u8;256],p:usize,j:usize)->bool{
 kani::assume(p<=224);kani::assume(j<32);
 let start=core::cmp::min(p,192);
 let rel=p-start;
 let window=&bytes[start..start+64];
 let actual=&bytes[p..p+32];
 let local=&window[rel..rel+32];
 !(rel<=32 && actual.len()==32 && window.len()==64 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(registry_array_wrong_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_array_wrong(){registry_array_wrong_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_array_packet(bytes:&[u8;320],p:usize,j:usize)->bool{
 kani::assume(p<=288);kani::assume(j<32);
 let start=core::cmp::min(p,256);
 let rel=p-start;
 let window=&bytes[start..start+64];
 let actual=&bytes[p..p+32];
 let local=&window[rel..rel+32];
 (rel<=32 && actual.len()==32 && window.len()==64 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(entry_array_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_array(){entry_array_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_array_wrong_packet(bytes:&[u8;320],p:usize,j:usize)->bool{
 kani::assume(p<=288);kani::assume(j<32);
 let start=core::cmp::min(p,256);
 let rel=p-start;
 let window=&bytes[start..start+64];
 let actual=&bytes[p..p+32];
 let local=&window[rel..rel+32];
 !(rel<=32 && actual.len()==32 && window.len()==64 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(entry_array_wrong_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_array_wrong(){entry_array_wrong_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_word_packet(bytes:&[u8;256],p:usize,j:usize)->bool{
 kani::assume(p<=248);kani::assume(j<8);
 let start=core::cmp::min(p,240);
 let rel=p-start;
 let window=&bytes[start..start+16];
 let actual=&bytes[p..p+8];
 let local=&window[rel..rel+8];
 (rel<=8 && actual.len()==8 && window.len()==16 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(registry_word_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_word(){registry_word_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_word_wrong_packet(bytes:&[u8;256],p:usize,j:usize)->bool{
 kani::assume(p<=248);kani::assume(j<8);
 let start=core::cmp::min(p,240);
 let rel=p-start;
 let window=&bytes[start..start+16];
 let actual=&bytes[p..p+8];
 let local=&window[rel..rel+8];
 !(rel<=8 && actual.len()==8 && window.len()==16 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(registry_word_wrong_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_word_wrong(){registry_word_wrong_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_word_packet(bytes:&[u8;320],p:usize,j:usize)->bool{
 kani::assume(p<=312);kani::assume(j<8);
 let start=core::cmp::min(p,304);
 let rel=p-start;
 let window=&bytes[start..start+16];
 let actual=&bytes[p..p+8];
 let local=&window[rel..rel+8];
 (rel<=8 && actual.len()==8 && window.len()==16 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(entry_word_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_word(){entry_word_packet(&kani::any(),kani::any(),kani::any());}

// Original decoder caller cut: no fabricated large slice, all legal offsets.
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_word_wrong_packet(bytes:&[u8;320],p:usize,j:usize)->bool{
 kani::assume(p<=312);kani::assume(j<8);
 let start=core::cmp::min(p,304);
 let rel=p-start;
 let window=&bytes[start..start+16];
 let actual=&bytes[p..p+8];
 let local=&window[rel..rel+8];
 !(rel<=8 && actual.len()==8 && window.len()==16 && actual.as_ptr()==local.as_ptr() && actual[j]==local[j])
}
#[kani::proof_for_contract(entry_word_wrong_packet)] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_word_wrong(){entry_word_wrong_packet(&kani::any(),kani::any(),kani::any());}



// NHY generated decoder cuts
fn registry_v1_header(bytes:&[u8])->u8{
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_BYTES {
        return 1;
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_MAGIC {
        return 2;
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_VERSION {
        return 3;
    }
    if bytes[7] != 0 || bytes[120..128] != [0u8; 8] {
        return 4;
    }
0}
fn registry_v1_header_ref(bytes:&[u8])->u8{if bytes.len()!=128 {1} else {if bytes[0]!=65 || bytes[1]!=83 || bytes[2]!=82 || bytes[3]!=71 {2} else {if bytes[4]!=2 {3} else {if bytes[7]!=0 || bytes[120]!=0 || bytes[121]!=0 || bytes[122]!=0 || bytes[123]!=0 || bytes[124]!=0 || bytes[125]!=0 || bytes[126]!=0 || bytes[127]!=0 {4} else {0}}}}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_v1_header_packet(bytes:&[u8;128])->bool{registry_v1_header(bytes)==registry_v1_header_ref(bytes)}
#[kani::proof_for_contract(registry_v1_header_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_v1_header_check(){registry_v1_header_packet(&kani::any());}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_v1_header_wrong_packet(bytes:&[u8;128])->bool{registry_v1_header(bytes)!=registry_v1_header_ref(bytes)}
#[kani::proof_for_contract(registry_v1_header_wrong_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_v1_header_wrong_check(){registry_v1_header_wrong_packet(&kani::any());}
fn entry_v1_header(bytes:&[u8])->u8{
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_BYTES {
        return 1;
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_MAGIC {
        return 2;
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_VERSION {
        return 3;
    }
    if bytes[184..192] != [0u8; 8] {
        return 4;
    }
0}
fn entry_v1_header_ref(bytes:&[u8])->u8{if bytes.len()!=192 {1} else {if bytes[0]!=65 || bytes[1]!=83 || bytes[2]!=82 || bytes[3]!=69 {2} else {if bytes[4]!=2 {3} else {if bytes[184]!=0 || bytes[185]!=0 || bytes[186]!=0 || bytes[187]!=0 || bytes[188]!=0 || bytes[189]!=0 || bytes[190]!=0 || bytes[191]!=0 {4} else {0}}}}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_v1_header_packet(bytes:&[u8;192])->bool{entry_v1_header(bytes)==entry_v1_header_ref(bytes)}
#[kani::proof_for_contract(entry_v1_header_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_v1_header_check(){entry_v1_header_packet(&kani::any());}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_v1_header_wrong_packet(bytes:&[u8;192])->bool{entry_v1_header(bytes)!=entry_v1_header_ref(bytes)}
#[kani::proof_for_contract(entry_v1_header_wrong_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_v1_header_wrong_check(){entry_v1_header_wrong_packet(&kani::any());}
fn registry_v2_header(bytes:&[u8])->u8{
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_V2_BYTES {
        return 1;
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_V2_MAGIC {
        return 2;
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_V2_VERSION {
        return 3;
    }
    if bytes[6] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return 4;
    }
    if bytes[249..256] != [0u8; 7] {
        return 5;
    }
0}
fn registry_v2_header_ref(bytes:&[u8])->u8{if bytes.len()!=256 {1} else {if bytes[0]!=65 || bytes[1]!=83 || bytes[2]!=82 || bytes[3]!=50 {2} else {if bytes[4]!=3 {3} else {if bytes[6]!=1 {4} else {if bytes[249]!=0 || bytes[250]!=0 || bytes[251]!=0 || bytes[252]!=0 || bytes[253]!=0 || bytes[254]!=0 || bytes[255]!=0 {5} else {0}}}}}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_v2_header_packet(bytes:&[u8;256])->bool{registry_v2_header(bytes)==registry_v2_header_ref(bytes)}
#[kani::proof_for_contract(registry_v2_header_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_v2_header_check(){registry_v2_header_packet(&kani::any());}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_v2_header_wrong_packet(bytes:&[u8;256])->bool{registry_v2_header(bytes)!=registry_v2_header_ref(bytes)}
#[kani::proof_for_contract(registry_v2_header_wrong_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_v2_header_wrong_check(){registry_v2_header_wrong_packet(&kani::any());}
fn entry_v2_header(bytes:&[u8])->u8{
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_V2_BYTES {
        return 1;
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_V2_MAGIC {
        return 2;
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_V2_VERSION {
        return 3;
    }
    if bytes[7] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return 4;
    }
    if bytes[314..320] != [0u8; 6] {
        return 5;
    }
0}
fn entry_v2_header_ref(bytes:&[u8])->u8{if bytes.len()!=320 {1} else {if bytes[0]!=65 || bytes[1]!=83 || bytes[2]!=69 || bytes[3]!=50 {2} else {if bytes[4]!=3 {3} else {if bytes[7]!=1 {4} else {if bytes[314]!=0 || bytes[315]!=0 || bytes[316]!=0 || bytes[317]!=0 || bytes[318]!=0 || bytes[319]!=0 {5} else {0}}}}}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_v2_header_packet(bytes:&[u8;320])->bool{entry_v2_header(bytes)==entry_v2_header_ref(bytes)}
#[kani::proof_for_contract(entry_v2_header_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_v2_header_check(){entry_v2_header_packet(&kani::any());}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_v2_header_wrong_packet(bytes:&[u8;320])->bool{entry_v2_header(bytes)!=entry_v2_header_ref(bytes)}
#[kani::proof_for_contract(entry_v2_header_wrong_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_v2_header_wrong_check(){entry_v2_header_wrong_packet(&kani::any());}

// NHY record cuts
fn NHY_any_error()->PoolV1VerifierRegistryFormatError{let tag:u8=kani::any();kani::assume(tag<12);match tag{0=>PoolV1VerifierRegistryFormatError::WrongLength,1=>PoolV1VerifierRegistryFormatError::WrongMagic,2=>PoolV1VerifierRegistryFormatError::WrongVersion,3=>PoolV1VerifierRegistryFormatError::NonZeroReserved,4=>PoolV1VerifierRegistryFormatError::UnsupportedFlags,5=>PoolV1VerifierRegistryFormatError::InvalidStatus,6=>PoolV1VerifierRegistryFormatError::InvalidAuthorityMode,7=>PoolV1VerifierRegistryFormatError::ZeroRequiredBinding,8=>PoolV1VerifierRegistryFormatError::InvalidActivationDelay,9=>PoolV1VerifierRegistryFormatError::InvalidStatementVersion,10=>PoolV1VerifierRegistryFormatError::InvalidRetirementSlot,_=>PoolV1VerifierRegistryFormatError::InvalidDeploymentMode}}
fn NHY_any_status()->VerifierEntryStatusV1{let tag:u8=kani::any();kani::assume(tag<4);match tag{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}
fn NHY_any_registry()->VerifierRegistryV2{VerifierRegistryV2{flags:kani::any(),bump:kani::any(),pool:kani::any(),authority:kani::any(),policy_binding:kani::any(),generation:kani::any(),minimum_activation_delay_slots:kani::any(),registry_program:kani::any(),loader_program:kani::any(),programdata_address:kani::any(),programdata_bump:kani::any(),executable_hash:kani::any()}}
fn NHY_registry_byte(r:&VerifierRegistryV2,field:u8,j:usize)->u8{match field{0=>r.pool[j],1=>r.authority[j],2=>r.policy_binding[j],3=>r.registry_program[j],4=>r.loader_program[j],5=>r.programdata_address[j],_=>r.executable_hash[j]}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_record_packet(input:&VerifierRegistryV2,reply:Result<(),PoolV1VerifierRegistryFormatError>,field:u8,j:usize)->bool{
 kani::assume((field as usize)<7);kani::assume(j<32);
    let registry = VerifierRegistryV2 {
        flags:input.flags,
        bump:input.bump,
        pool:input.pool,
        authority:input.authority,
        policy_binding:input.policy_binding,
        generation:input.generation,
        minimum_activation_delay_slots:input.minimum_activation_delay_slots,
        registry_program:input.registry_program,
        loader_program:input.loader_program,
        programdata_address:input.programdata_address,
        programdata_bump:input.programdata_bump,
        executable_hash:input.executable_hash,
    };
 let mut calls=0u8;
 let result=(||->Result<VerifierRegistryV2,PoolV1VerifierRegistryFormatError>{
  // Exact local logging oracle: immutable input record, full Result reply.
  calls+=1;
  let validation=reply;
  validation?;
  Ok(registry)
 })();
 let value=match (reply,&result){
  (Err(e),Err(observed))=>e==*observed,
  (Ok(()),Ok(observed))=>NHY_registry_byte(observed,field,j)==NHY_registry_byte(input,field,j)
    && observed.flags==input.flags
    && observed.bump==input.bump
    && observed.generation==input.generation
    && observed.minimum_activation_delay_slots==input.minimum_activation_delay_slots
    && observed.programdata_bump==input.programdata_bump
  ,_=>false};
 calls==1 && value
}
#[kani::proof_for_contract(registry_record_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_record_check(){let input=NHY_any_registry();let reply=if kani::any(){Ok(())}else{Err(NHY_any_error())};registry_record_packet(&input,reply,kani::any(),kani::any());}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn registry_record_wrong_packet(input:&VerifierRegistryV2,reply:Result<(),PoolV1VerifierRegistryFormatError>,field:u8,j:usize)->bool{
 kani::assume((field as usize)<7);kani::assume(j<32);
    let registry = VerifierRegistryV2 {
        flags:input.flags,
        bump:input.bump,
        pool:input.pool,
        authority:input.authority,
        policy_binding:input.policy_binding,
        generation:input.generation,
        minimum_activation_delay_slots:input.minimum_activation_delay_slots,
        registry_program:input.registry_program,
        loader_program:input.loader_program,
        programdata_address:input.programdata_address,
        programdata_bump:input.programdata_bump,
        executable_hash:input.executable_hash,
    };
 let mut calls=0u8;
 let result=(||->Result<VerifierRegistryV2,PoolV1VerifierRegistryFormatError>{
  // Exact local logging oracle: immutable input record, full Result reply.
  calls+=1;
  let validation=reply;
  validation?;
  Ok(registry)
 })();
 let value=match (reply,&result){
  (Err(e),Err(observed))=>e==*observed,
  (Ok(()),Ok(observed))=>NHY_registry_byte(observed,field,j)==NHY_registry_byte(input,field,j)
    && observed.flags==input.flags
    && observed.bump==input.bump
    && observed.generation==input.generation
    && observed.minimum_activation_delay_slots==input.minimum_activation_delay_slots
    && observed.programdata_bump==input.programdata_bump
  ,_=>false};
 calls==2 && value
}
#[kani::proof_for_contract(registry_record_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_record_wrong_check(){let input=NHY_any_registry();let reply=if kani::any(){Ok(())}else{Err(NHY_any_error())};registry_record_wrong_packet(&input,reply,kani::any(),kani::any());}
fn NHY_any_entry()->VerifierRegistryEntryV2{VerifierRegistryEntryV2{status:NHY_any_status(),statement_version:kani::any(),bump:kani::any(),pool:kani::any(),verifier_program:kani::any(),profile_binding:kani::any(),release_binding:kani::any(),loader_program:kani::any(),programdata_address:kani::any(),programdata_bump:kani::any(),executable_hash:kani::any(),expected_upgrade_authority:kani::any(),activation_slot:kani::any(),retirement_slot:kani::any(),policy_binding:kani::any()}}
fn NHY_entry_byte(r:&VerifierRegistryEntryV2,field:u8,j:usize)->u8{match field{0=>r.pool[j],1=>r.verifier_program[j],2=>r.profile_binding[j],3=>r.release_binding[j],4=>r.loader_program[j],5=>r.programdata_address[j],6=>r.executable_hash[j],7=>r.expected_upgrade_authority[j],_=>r.policy_binding[j]}}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_record_packet(input:&VerifierRegistryEntryV2,reply:Result<(),PoolV1VerifierRegistryFormatError>,field:u8,j:usize)->bool{
 kani::assume((field as usize)<9);kani::assume(j<32);
    let entry = VerifierRegistryEntryV2 {
        status:input.status,
        statement_version:input.statement_version,
        bump:input.bump,
        pool:input.pool,
        verifier_program:input.verifier_program,
        profile_binding:input.profile_binding,
        release_binding:input.release_binding,
        loader_program:input.loader_program,
        programdata_address:input.programdata_address,
        programdata_bump:input.programdata_bump,
        executable_hash:input.executable_hash,
        expected_upgrade_authority:input.expected_upgrade_authority,
        activation_slot:input.activation_slot,
        retirement_slot:input.retirement_slot,
        policy_binding:input.policy_binding,
    };
 let mut calls=0u8;
 let result=(||->Result<VerifierRegistryEntryV2,PoolV1VerifierRegistryFormatError>{
  // Exact local logging oracle: immutable input record, full Result reply.
  calls+=1;
  let validation=reply;
  validation?;
  Ok(entry)
 })();
 let value=match (reply,&result){
  (Err(e),Err(observed))=>e==*observed,
  (Ok(()),Ok(observed))=>NHY_entry_byte(observed,field,j)==NHY_entry_byte(input,field,j)
    && observed.status==input.status
    && observed.statement_version==input.statement_version
    && observed.bump==input.bump
    && observed.programdata_bump==input.programdata_bump
    && observed.activation_slot==input.activation_slot
    && observed.retirement_slot==input.retirement_slot
  ,_=>false};
 calls==1 && value
}
#[kani::proof_for_contract(entry_record_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_record_check(){let input=NHY_any_entry();let reply=if kani::any(){Ok(())}else{Err(NHY_any_error())};entry_record_packet(&input,reply,kani::any(),kani::any());}
#[kani::ensures(|r|*r)] #[kani::modifies()]
fn entry_record_wrong_packet(input:&VerifierRegistryEntryV2,reply:Result<(),PoolV1VerifierRegistryFormatError>,field:u8,j:usize)->bool{
 kani::assume((field as usize)<9);kani::assume(j<32);
    let entry = VerifierRegistryEntryV2 {
        status:input.status,
        statement_version:input.statement_version,
        bump:input.bump,
        pool:input.pool,
        verifier_program:input.verifier_program,
        profile_binding:input.profile_binding,
        release_binding:input.release_binding,
        loader_program:input.loader_program,
        programdata_address:input.programdata_address,
        programdata_bump:input.programdata_bump,
        executable_hash:input.executable_hash,
        expected_upgrade_authority:input.expected_upgrade_authority,
        activation_slot:input.activation_slot,
        retirement_slot:input.retirement_slot,
        policy_binding:input.policy_binding,
    };
 let mut calls=0u8;
 let result=(||->Result<VerifierRegistryEntryV2,PoolV1VerifierRegistryFormatError>{
  // Exact local logging oracle: immutable input record, full Result reply.
  calls+=1;
  let validation=reply;
  validation?;
  Ok(entry)
 })();
 let value=match (reply,&result){
  (Err(e),Err(observed))=>e==*observed,
  (Ok(()),Ok(observed))=>NHY_entry_byte(observed,field,j)==NHY_entry_byte(input,field,j)
    && observed.status==input.status
    && observed.statement_version==input.statement_version
    && observed.bump==input.bump
    && observed.programdata_bump==input.programdata_bump
    && observed.activation_slot==input.activation_slot
    && observed.retirement_slot==input.retirement_slot
  ,_=>false};
 calls==2 && value
}
#[kani::proof_for_contract(entry_record_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn entry_record_wrong_check(){let input=NHY_any_entry();let reply=if kani::any(){Ok(())}else{Err(NHY_any_error())};entry_record_wrong_packet(&input,reply,kani::any(),kani::any());}
