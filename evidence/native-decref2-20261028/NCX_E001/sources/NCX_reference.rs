// Safe reference derived from frozen current registry source.
pub const POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK:u8=3;
pub const POOL_V1_VERIFIER_REGISTRY_MAGIC: [u8; 4] = *b"ASRG";

pub const POOL_V1_VERIFIER_REGISTRY_VERSION: u8 = 2;

pub const POOL_V1_VERIFIER_REGISTRY_BYTES: usize = 128;

pub const POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED: u8 = 1 << 0;

pub const POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE: u8 = 1 << 1;

pub const POOL_V1_VERIFIER_ENTRY_MAGIC: [u8; 4] = *b"ASRE";

pub const POOL_V1_VERIFIER_ENTRY_VERSION: u8 = 2;

pub const POOL_V1_VERIFIER_ENTRY_BYTES: usize = 192;

pub const POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT: u64 = u64::MAX;

pub const POOL_V1_VERIFIER_REGISTRY_V2_MAGIC: [u8; 4] = *b"ASR2";

pub const POOL_V1_VERIFIER_REGISTRY_V2_VERSION: u8 = 3;

pub const POOL_V1_VERIFIER_REGISTRY_V2_BYTES: usize = 256;

pub const POOL_V1_VERIFIER_ENTRY_V2_MAGIC: [u8; 4] = *b"ASE2";

pub const POOL_V1_VERIFIER_ENTRY_V2_VERSION: u8 = 3;

pub const POOL_V1_VERIFIER_ENTRY_V2_BYTES: usize = 320;

pub const POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3: u8 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1VerifierRegistryFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    UnsupportedFlags,
    InvalidStatus,
    InvalidAuthorityMode,
    ZeroRequiredBinding,
    InvalidActivationDelay,
    InvalidStatementVersion,
    InvalidRetirementSlot,
    InvalidDeploymentMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifierEntryStatusV1 {
    Pending = 0,
    Active = 1,
    Paused = 2,
    Retired = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRegistryV2 {
    pub flags: u8,
    /// Canonical registry PDA bump established by initialization.
    pub bump: u8,
    pub pool: [u8; 32],
    pub authority: [u8; 32],
    pub policy_binding: [u8; 32],
    pub generation: u64,
    pub minimum_activation_delay_slots: u64,
    pub registry_program: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    /// Canonical loader-v3 ProgramData bump established by deployment authentication.
    pub programdata_bump: u8,
    pub executable_hash: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierRegistryEntryV2 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    /// Canonical loader-v3 ProgramData bump established by deployment authentication.
    pub programdata_bump: u8,
    pub executable_hash: [u8; 32],
    /// Production V2 requires this to be all zero, denoting `None`.
    pub expected_upgrade_authority: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}

pub fn read32(b:&[u8],p:usize)->[u8;32] {let mut a=[0u8;32];let mut i=0;while i<32 {a[i]=b[p+i];i+=1;}a}
pub fn word(b:&[u8],p:usize)->u64 {let mut a=0u64;let mut i=0;while i<8 {a|=(b[p+i] as u64) << (8*i);i+=1;}a}
pub fn zero(b:&[u8],p:usize,n:usize)->bool {let mut i=0;while i<n {if b[p+i]!=0{return false;}i+=1;}true}
pub fn magic(b:&[u8],m:[u8;4])->bool {b[0]==m[0] && b[1]==m[1] && b[2]==m[2] && b[3]==m[3]}
pub fn required_binding_is_zero(b:&[u8;32])->bool {zero(b,0,32)}
pub fn status(v:u8)->Result<VerifierEntryStatusV1,PoolV1VerifierRegistryFormatError> {match v {0=>Ok(VerifierEntryStatusV1::Pending),1=>Ok(VerifierEntryStatusV1::Active),2=>Ok(VerifierEntryStatusV1::Paused),3=>Ok(VerifierEntryStatusV1::Retired),_=>Err(PoolV1VerifierRegistryFormatError::InvalidStatus)}}

pub fn validate_verifier_registry_v2(
    registry: &VerifierRegistryV2,
) -> Result<(), PoolV1VerifierRegistryFormatError> {
    if registry.flags & !POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK != 0 {
        return Err(PoolV1VerifierRegistryFormatError::UnsupportedFlags);
    }
    if required_binding_is_zero(&registry.pool)
        || required_binding_is_zero(&registry.policy_binding)
        || required_binding_is_zero(&registry.registry_program)
        || required_binding_is_zero(&registry.loader_program)
        || required_binding_is_zero(&registry.programdata_address)
        || required_binding_is_zero(&registry.executable_hash)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if (registry.flags & 2 != 0) != required_binding_is_zero(&registry.authority) {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if registry.minimum_activation_delay_slots == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidActivationDelay);
    }
    Ok(())
}

pub fn validate_verifier_registry_entry_v2(
    entry: &VerifierRegistryEntryV2,
) -> Result<(), PoolV1VerifierRegistryFormatError> {
    if entry.statement_version == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidStatementVersion);
    }
    if required_binding_is_zero(&entry.pool)
        || required_binding_is_zero(&entry.verifier_program)
        || required_binding_is_zero(&entry.profile_binding)
        || required_binding_is_zero(&entry.release_binding)
        || required_binding_is_zero(&entry.loader_program)
        || required_binding_is_zero(&entry.programdata_address)
        || required_binding_is_zero(&entry.executable_hash)
        || required_binding_is_zero(&entry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if !required_binding_is_zero(&entry.expected_upgrade_authority) {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if !(entry.retirement_slot == u64::MAX) && entry.retirement_slot <= entry.activation_slot {
        return Err(PoolV1VerifierRegistryFormatError::InvalidRetirementSlot);
    }
    Ok(())
}

pub fn decode_verifier_registry_v2(
    bytes: &[u8],
) -> Result<VerifierRegistryV2, PoolV1VerifierRegistryFormatError> {
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_V2_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if !magic(bytes,POOL_V1_VERIFIER_REGISTRY_V2_MAGIC) {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_V2_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[6] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode);
    }
    if !zero(bytes,249,7) {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let registry = VerifierRegistryV2 {
        flags: bytes[5],
        bump: bytes[7],
        pool: read32(bytes,8),
        authority: read32(bytes,40),
        policy_binding: read32(bytes,72),
        generation: word(bytes,104),
        minimum_activation_delay_slots: word(bytes,112),
        registry_program: read32(bytes,120),
        loader_program: read32(bytes,152),
        programdata_address: read32(bytes,184),
        programdata_bump: bytes[248],
        executable_hash: read32(bytes,216),
    };
    validate_verifier_registry_v2(&registry)?;
    Ok(registry)
}

pub fn decode_verifier_registry_entry_v2(
    bytes: &[u8],
) -> Result<VerifierRegistryEntryV2, PoolV1VerifierRegistryFormatError> {
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_V2_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if !magic(bytes,POOL_V1_VERIFIER_ENTRY_V2_MAGIC) {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_V2_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[7] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode);
    }
    if !zero(bytes,314,6) {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let entry = VerifierRegistryEntryV2 {
        status: status(bytes[5])?,
        statement_version: bytes[6],
        bump: bytes[312],
        pool: read32(bytes,8),
        verifier_program: read32(bytes,40),
        profile_binding: read32(bytes,72),
        release_binding: read32(bytes,104),
        loader_program: read32(bytes,136),
        programdata_address: read32(bytes,168),
        programdata_bump: bytes[313],
        executable_hash: read32(bytes,200),
        expected_upgrade_authority: read32(bytes,232),
        activation_slot: word(bytes,264),
        retirement_slot: word(bytes,272),
        policy_binding: read32(bytes,280),
    };
    validate_verifier_registry_entry_v2(&entry)?;
    Ok(entry)
}
