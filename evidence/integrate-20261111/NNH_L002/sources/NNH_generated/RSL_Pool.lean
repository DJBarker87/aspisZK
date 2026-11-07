/-
RSL_Pool: Pool/registry carriers, frozen constants and the CLOSED-child model
interface used by the TX2 adapter rows (217, 234, 233, 242, 241) and TX1:345.

Structures transcribe aspis-statement at 4bb3b3f5 field-for-field
(pair_forest_accounts.rs:127-158, verifier_registry.rs:79-185,
incremental_merkle.rs:64, pair_tree_profile.rs:404).

`PoolLib` collects the CLOSED children that the adapter rows call but that are
not re-transcribed here.  It is NOT a free Ops dictionary at a root (ruling
(au)): every field has exactly one admissible instantiation, named in its
comment, namely the model function of that CLOSED row's root at SAME
arguments.  A CLOSED child's own (bf)(2) domain, if its root has one, is folded
into the Spec-valued field (`fun a env o => Dom a ∧ Law a env o`), so a parent
RowSpec instantiated that way must discharge it.  The next ledger gate checks
each instantiation clause by clause.
-/
import RSL_Base
set_option autoImplicit false

namespace RSL

/-! ## Constants (frozen values) -/

def LANE_HEADER_BYTES : Nat := 80
def TREE_DEPTH : Nat := 20
def TREE_STATE_BYTES : Nat := 48 + 32 * TREE_DEPTH            -- 688
def LANE_ACCOUNT_BYTES : Nat := LANE_HEADER_BYTES + TREE_STATE_BYTES  -- 768
def LANE_COUNT : Nat := 8
def PAIR_CAPACITY : UInt64 := 1048576  -- 1u64 << 20
def AFTERSTATE_BYTES : Nat := 688
def PROOF_BYTES : Nat := 57607
def PROOF_ACCOUNT_BYTES : Nat := AFTERSTATE_BYTES + PROOF_BYTES   -- 58295
def STATEMENT_BYTES : Nat := 1880
def MASTER_ACCOUNT_BYTES : Nat := 384
def CHECKPOINT_ACCOUNT_BYTES : Nat := 192
def REGISTRY_BYTES : Nat := 128
def REGISTRY_V2_BYTES : Nat := 256
def ENTRY_BYTES : Nat := 192
def ENTRY_V2_BYTES : Nat := 320
def REQUEST_BYTES : Nat := 320


def LANE_MAGIC : Bytes := [65, 83, 76, 56]  -- b"ASL8"
def LANE_VERSION : UInt8 := 2
def TREE_STATE_MAGIC : Bytes := [65, 83, 80, 84]  -- b"ASPT"
def TREE_STATE_VERSION : UInt8 := 1
def TREE_HASH_VERSION : UInt8 := 3
def DIGEST_ENCODING_VERSION : UInt8 := 1
def REQUEST_MAGIC : Bytes := [65, 83, 81, 56]  -- b"ASQ8"
def FORMAT_BINDING : Bytes :=
  [65, 83, 80, 73, 83, 70, 79, 82, 69, 83, 84, 56] ++ [2, 2, 2, 8, 1, 20, 1] ++ List.replicate 13 0
def ALL_LANES_MASK : UInt8 := 0xff
def POLICY_FLAG_IMMUTABLE_REGISTRY : UInt8 := 1
def POLICY_FLAG_IMMUTABLE_DEPLOYMENT : UInt8 := 2
def REGISTRY_FLAG_PAUSED : UInt8 := 1
def REGISTRY_FLAG_IMMUTABLE : UInt8 := 2
def TERMINAL_VERSION : UInt8 := 1
def NO_RETIREMENT_SLOT : UInt64 := 0xffffffffffffffff

def AUDIT_POLICY_BINDING : B32 := B32.ofFill 7

def mkB32 (l : List UInt8) (h : l.length = 32) : B32 := ⟨l, h⟩

/-- private-leaf-salts PROFILE_BINDING (r1_pool_adapter.rs:67-71). -/
def PROFILE_BINDING : B32 := mkB32
  [0x57,0x94,0x73,0x13,0xd2,0x32,0x64,0x1a,0xd8,0x15,0x7d,0x66,0xbf,0xaf,0xfa,0xb1,
   0x1e,0x4c,0x3a,0x99,0x33,0x1d,0x18,0xf4,0x4b,0xfa,0xca,0xb6,0x89,0x97,0x37,0xd3] rfl
/-- private-leaf-salts RELEASE_BINDING (r1_pool_adapter.rs:72-76). -/
def RELEASE_BINDING : B32 := mkB32
  [0xe2,0x94,0xaf,0xbc,0x14,0xef,0x6a,0xfe,0x76,0xb8,0x47,0xde,0xf4,0x44,0x52,0xf8,
   0x4c,0xc3,0x72,0x80,0x64,0x65,0x76,0x07,0xb5,0x44,0xa5,0x39,0xca,0x9b,0x32,0x3a] rfl
/-- `bpf_loader_upgradeable::id()` = BPFLoaderUpgradeab1e11111111111111111111111. -/
def LOADER_ID : B32 := mkB32
  [2,168,246,145,78,136,161,176,226,16,21,62,247,99,174,43,0,194,185,61,22,193,36,210,
   192,83,122,16,4,128,0,0] rfl

def SEED_MASTER : Bytes := [97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 109, 97, 115, 116, 101, 114, 45, 118, 49]  -- b"aspis-pair-forest-master-v1"
def SEED_LANE : Bytes := [97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 108, 97, 110, 101, 45, 118, 49]  -- b"aspis-pair-forest-lane-v1"
def SEED_CHECKPOINT : Bytes := [97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 99, 104, 101, 99, 107, 112, 111, 105, 110, 116, 45, 118, 49]  -- b"aspis-pair-forest-checkpoint-v1"
def SEED_REGISTRY : Bytes := [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 114, 101, 103, 105, 115, 116, 114, 121, 45, 118, 49]  -- b"aspis-verifier-registry-v1"
def SEED_ENTRY : Bytes := [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 101, 110, 116, 114, 121, 45, 118, 49]  -- b"aspis-verifier-entry-v1"
def SEED_REGISTRY_V2 : Bytes := [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 114, 101, 103, 105, 115, 116, 114, 121, 45, 118, 50]  -- b"aspis-verifier-registry-v2"
def SEED_ENTRY_V2 : Bytes := [97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 101, 110, 116, 114, 121, 45, 118, 50]  -- b"aspis-verifier-entry-v2"

/-- V7_PAIR_EMPTY_ROOTS (programs/aspis-verifier/src/v7_pair_empty_roots.rs). -/
def EMPTY_ROOTS : List Digest := [
  [1438900896, 782233260, 1544844157, 891350894, 986827501, 300047813, 266092546, 1155026732],
  [141619947, 1448060902, 524379093, 1944458907, 1832113773, 579270723, 752346270, 1038346536],
  [1119858538, 128294437, 939091034, 659145897, 1933666768, 903679201, 1182639487, 1398246146],
  [1057897051, 1132946363, 794377079, 1971564389, 1255722275, 926653737, 2031728153, 2024887573],
  [1410054462, 673771449, 940847521, 274330358, 1719505495, 1690439941, 203201419, 1855504616],
  [1442759752, 1540325866, 188964047, 101815282, 1883549730, 1774537487, 1306717763, 561084592],
  [244193611, 984304317, 1467689208, 2063463197, 1766003332, 1300835127, 1578947755, 745931587],
  [673192756, 38070812, 1453532835, 1340577407, 368420458, 1834405704, 270061815, 711700631],
  [27092219, 1272373356, 998194489, 1458413288, 887470405, 1204987730, 864453460, 553704718],
  [1972918328, 1234090299, 977162835, 1704494754, 1617603773, 1819200880, 906453206, 1653526885],
  [418360492, 472096212, 871749117, 98906847, 2026788776, 1504737042, 407274798, 1800828893],
  [986339640, 660349625, 1012157959, 454024326, 987656904, 622864739, 1150440730, 1280042062],
  [2118470693, 1706590589, 2128512933, 167263577, 409542414, 1323179656, 1880070613, 2053396184],
  [260546973, 1375125357, 1584234519, 1097072342, 1685367984, 1070989054, 2113798037, 958210542],
  [1239966481, 992485427, 1397515674, 466658549, 2071909237, 712995354, 2047452742, 1680224983],
  [1796237568, 1862343136, 1954463912, 1190686266, 364700025, 46960257, 671215600, 1214723477],
  [1127845264, 662862400, 84021756, 995080286, 1419670571, 1966281459, 837284626, 2083375353],
  [1321679286, 782621548, 1415820264, 74436574, 776350425, 323154748, 429051705, 1299980413],
  [1519171444, 1235587172, 1671492368, 1449613582, 547369941, 1621086153, 266860322, 450526803],
  [19381883, 1308966873, 251977766, 474343397, 2069732268, 1863820229, 152153379, 665567443],
  [1201428963, 1296676114, 441891487, 1910121140, 602621674, 1294160489, 1878016864, 855887413]]

/-! ## Carriers -/

structure PoolIdentity where
  pool : B32
  asset_mint : B32
  token_program : B32
  asset_id : UInt32
  deployment_domain : B32

structure VerifierPolicy where
  flags : UInt8
  registry_program : B32
  registry_authority : B32
  policy_binding : B32

structure Master where
  bump : UInt8
  identity : PoolIdentity
  verifier_policy : VerifierPolicy
  initialized_lane_mask : UInt8
  has_checkpoint : Bool
  next_checkpoint_sequence : UInt64
  last_checkpoint_lane_sequences : List UInt64

structure Checkpoint where
  bump : UInt8
  master : B32
  deployment_domain : B32
  checkpoint_sequence : UInt64
  global_root : Digest
  lane_sequences : List UInt64

structure Tree where
  next_leaf_index : UInt64
  root : Digest
  frontier : List Digest

structure LaneState where
  bump : UInt8
  master : B32
  lane_id : UInt8
  tree : Tree

structure LiveSnapshot where
  pool : B32
  deployment_domain : B32
  sequence : UInt64
  next_pair_index : UInt64
  current_root : Digest
  frontier : List Digest

inductive EntryStatus where
  | pending | active | paused | retired
  deriving DecidableEq

structure RegistryV1 where
  flags : UInt8
  bump : UInt8
  pool : B32
  authority : B32
  policy_binding : B32
  generation : UInt64
  minimum_activation_delay_slots : UInt64

structure RegistryV2 where
  flags : UInt8
  bump : UInt8
  pool : B32
  authority : B32
  policy_binding : B32
  generation : UInt64
  minimum_activation_delay_slots : UInt64
  registry_program : B32
  loader_program : B32
  programdata_address : B32
  programdata_bump : UInt8
  executable_hash : B32

structure EntryV1 where
  status : EntryStatus
  statement_version : UInt8
  bump : UInt8
  pool : B32
  verifier_program : B32
  profile_binding : B32
  release_binding : B32
  activation_slot : UInt64
  retirement_slot : UInt64
  policy_binding : B32

structure EntryV2 where
  status : EntryStatus
  statement_version : UInt8
  bump : UInt8
  pool : B32
  verifier_program : B32
  profile_binding : B32
  release_binding : B32
  loader_program : B32
  programdata_address : B32
  programdata_bump : UInt8
  executable_hash : B32
  expected_upgrade_authority : B32
  activation_slot : UInt64
  retirement_slot : UInt64
  policy_binding : B32

/-- `is_paused` / `is_immutable` (CLOSED TX2:197-200). -/
def RegistryV1.is_paused (r : RegistryV1) : Bool := r.flags &&& REGISTRY_FLAG_PAUSED != 0
def RegistryV1.is_immutable (r : RegistryV1) : Bool := r.flags &&& REGISTRY_FLAG_IMMUTABLE != 0
def RegistryV2.is_paused (r : RegistryV2) : Bool := r.flags &&& REGISTRY_FLAG_PAUSED != 0
def RegistryV2.is_immutable (r : RegistryV2) : Bool := r.flags &&& REGISTRY_FLAG_IMMUTABLE != 0

/-- `is_active_at` (CLOSED TX2:194 / TX2:196, NIS_ActiveSlots). -/
def EntryV1.is_active_at (e : EntryV1) (slot : UInt64) : Bool :=
  e.status == .active && decide (e.activation_slot ≤ slot) &&
    (e.retirement_slot == NO_RETIREMENT_SLOT || decide (slot < e.retirement_slot))
def EntryV2.is_active_at (e : EntryV2) (slot : UInt64) : Bool :=
  e.status == .active && decide (e.activation_slot ≤ slot) &&
    (e.retirement_slot == NO_RETIREMENT_SLOT || decide (slot < e.retirement_slot))

/-- `AuthenticatedAsq8Accounts` (r1_pool_adapter.rs:150-158).  The four Box
fields are owned fresh objects; each is created at its own allocation site in
the reference, and none is erased from the returned value (NMG/NLW finding on
the NLM drafts).  Their later drop writes no account or return data and is
outside the obligation under (bl)(3). -/
structure Authenticated where
  master_account : B32
  checkpoint_account : B32
  selected_lane_account : B32
  master : Master
  checkpoint : Checkpoint
  selected_lane : LaneState
  live_snapshot : LiveSnapshot

/-! ## CLOSED child models -/

structure PoolLib where
  /-- Opaque statement-crate carriers (values flow through unchanged). -/
  Request : Type
  Statement : Type
  Afterstate : Type
  /-- `decode_pool_v1_pair_forest_terminal_request_v1` (CLOSED TX2:163, NFY_Part059). -/
  decodeRequest : Bytes → Option Request
  /-- Field reads `request.verifier_profile/verifier_release/pool_program`. -/
  reqProfile : Request → B32
  reqRelease : Request → B32
  reqPoolProgram : Request → B32
  /-- `request.public.nullifier()` (CLOSED TX2:158, NGE_NEQ_NullifierDomains). -/
  reqNullifier : Request → B32
  /-- `pool_v1_pair_forest_output_lane_v1` (CLOSED TX2:156, NFY_Part031). -/
  outputLane : B32 → Option UInt8
  /-- The decoder inside `decode_master_box` (CLOSED TX2:218, NKY_BoxSource). -/
  decodeMaster : Bytes → Option Master
  /-- The decoder inside `decode_checkpoint_box` (CLOSED TX2:216, NKY_BoxSource). -/
  decodeCheckpoint : Bytes → Option Checkpoint
  /-- `validate_verifier_policy_v1(..).is_ok()` (CLOSED TX2:151, NHY_PolicyModel). -/
  validatePolicy : VerifierPolicy → Bool
  /-- Registry/entry decoders (CLOSED TX2:203 NJY_Roots, TX2:204 NHY_RegistryJoin,
  TX2:201 NJY_Roots, TX2:202 NIS_EntryJoin). -/
  decodeRegistryV1 : Bytes → Option RegistryV1
  decodeRegistryV2 : Bytes → Option RegistryV2
  decodeEntryV1 : Bytes → Option EntryV1
  decodeEntryV2 : Bytes → Option EntryV2
  /-- `scan_proof_buffer` (CLOSED TX2:226, NFY_Part060): complete Result incl.
  its Box allocation; returns (candidate_afterstate, proof_length). -/
  scanProof : Bytes → RS (Afterstate × Nat)
  /-- `reconstruct_asq8_statement` (CLOSED TX2:224, NFY_Part057). -/
  reconstruct : Request → Authenticated → Afterstate → RS Statement
  /-- `encode_pool_v1_pair_forest_terminal_statement_v1(..).map_err(|_| ..)`
  (CLOSED TX2:165, NFY_Part053): `none` = encoder Err.  The frozen encoder
  returns `[u8; 1880]` by value (pair_forest_terminal.rs:292-329) and has no heap
  allocation site; an abort arm here may come only from that CLOSED law
  (Revision 2 correction of this comment; the type is unchanged). -/
  encodeStatement : Statement → Spec (Option Bytes)
  /-- `emit_result` (CLOSED TX2:219, NFY_Part058): complete Result and its
  `returnData` event. -/
  emitResult : Statement → RS Unit

/-- Deployed identifiers read from .rodata (CLOSED TX2:220 / TX2:225,
NHJ_DeployedIds); instantiated with the release-pinned values. -/
structure DeployedIds where
  pool : B32
  registry : B32

/-- One `Pubkey::create_program_address` syscall: event with its reply. -/
def pdaCall (seeds : List Bytes) (program : B32) : Spec (Option B32) :=
  Spec.bind (Spec.env (fun e => e.pda seeds program)) (fun r =>
    Spec.bind (Spec.emit (.pda seeds program r)) (fun _ => Spec.pure r))

/-- `create_program_address(..).map_err(|_| InvalidAccountData)?`. -/
def pdaOrErr (seeds : List Bytes) (program : B32) : RS B32 :=
  RS.bind (RS.lift (pdaCall seeds program)) (fun r => RS.ofOption r .invalidAccountData)

/-- `decode_master_box` body: decode (Err -> InvalidAccountData), then Box. -/
def decodeMasterBox (L : PoolLib) (b : Bytes) : RS Master :=
  RS.bind (RS.ofOption (L.decodeMaster b) .invalidAccountData) (fun m =>
    RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure m))

/-- `decode_checkpoint_box` body. -/
def decodeCheckpointBox (L : PoolLib) (b : Bytes) : RS Checkpoint :=
  RS.bind (RS.ofOption (L.decodeCheckpoint b) .invalidAccountData) (fun c =>
    RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure c))

end RSL
