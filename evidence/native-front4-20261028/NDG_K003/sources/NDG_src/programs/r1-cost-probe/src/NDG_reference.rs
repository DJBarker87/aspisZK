pub fn identity_key_ref(key: &[u8;32]) -> &[u8;32] { key }
pub fn readonly_buffer_ref(signer:bool,writable:bool,executable:bool)->bool {
    !(signer || writable || executable)
}
pub fn readonly_ref(different:bool,signer:bool,writable:bool,executable:bool)->bool {
    !(different || signer || writable || executable)
}
pub fn pool_id_ref()->[u8;32] { [0x41;32] }
pub fn registry_id_ref()->[u8;32] { [0x44;32] }
