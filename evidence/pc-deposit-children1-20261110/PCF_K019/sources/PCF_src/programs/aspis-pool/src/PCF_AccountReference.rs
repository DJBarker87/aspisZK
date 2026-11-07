// Value-only references. Zero denotes Ok; each nonzero value is the exact Custom payload.
pub fn payer_reference(signer:bool,writable:bool,executable:bool,system_owner:bool,
    system_key:bool,native_owner:bool,system_executable:bool,system_signer:bool,system_writable:bool)->u32 {
    if !signer || !writable || executable || !system_owner {0x41532034}
    else if !system_key || !native_owner || !system_executable || system_signer || system_writable {0x41532033}
    else {0}
}
pub fn token_reference(token_key:bool,executable:bool,signer:bool,writable:bool,
    bpf_owner:bool,upgradeable_owner:bool,v4_owner:bool)->u32 {
    if !token_key || !executable || signer || writable || !(bpf_owner || upgradeable_owner || v4_owner) {0x41532013}
    else {0}
}
pub fn count_reference(count:usize,expected:usize)->u8 {
    if count != expected {if count<expected {1} else {2}} else {0}
}
