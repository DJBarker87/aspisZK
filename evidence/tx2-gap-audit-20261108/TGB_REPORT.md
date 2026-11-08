# TGB: pre-emptive spec-versus-library audit for TX2:233, 242, 241, 240, 221, 213

Target not yet established. This is a read-only audit. It closes no row, changes no
RowSpec, library, ledger, trust row or frozen source, and adds no hypothesis.

Base: research def3eee1fa1. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Inputs read with `git show research:<path>`: RSL rev4 (RSL_REVISION2/3/4.md,
RSL_TX2_213/217/221/233/234/240/241/242, RSL_Base, RSL_Pool, RSL_LEDGER_CLAUSES.json);
LIBB V0-star (LIBB_V2Star, LIBB_V2Lib, LIBB_Tx2Auth, LIBB_Tx2Domain, LIBB_Tx2AuthGate,
LIBB_PoolLib and its PoolEffects/Scan/ScannerExtent/Reconstruct/Encode/Emit/Decoders/
Accounts/AuthCarrier/AccountCarriers/PartitionEnv); LIB_FullInstances; NMS_ (R2Fold241,
R2Weak241, R2SiteWeak241, R2Replay241, R2Validate241, R2Reads241, R2Domains,
R2Facts242, R2AuthFacts, REMAINING); NMX_ (242_241_READINESS, R2_DecoderLibrary,
R2_Carrier, OwnedPackets); NMV_ (CandidateRoots, NNCWeak, WindowClock,
ConcreteWindows, REMAINING); NNF_ (Folds, REMAINING); TCK_REPORT, TCK_WeakRoot0;
NNC_ObservedLaw, NNC_ObservedWeak, NNC_WriteFree, NNC_REMAINING; NND_ carriers;
TAS_Interfaces.Refines064; ledger27 NNK_REMAINING / NNK_CLAUSE_REVIEW; the frozen
r1_pool_adapter_owned.rs, r1_pool_adapter.rs (scan/reconstruct/emit/decoders/process),
lib.rs, pool_route.rs, verifier.rs constants, and the vendored ProgramError source
(NMS_SDK_PROGRAM_ERROR.rs.txt). No Lean, Kani or host job was run: every statement
below is from reading source.

Classification key (from the brief): (i) missing own-input or caller fact that the
caller supplies; (ii) library domain too strong, needs a total law; (iii) genuine
spec or registration error; (iv) real obstruction.

## 1. Result

No RowSpec-level domain gap was found in the RSL chain 213 → 221 → 240 → 241 → 242 →
233 → {217, 234}. Every `Spec.call` occurrence has its child's `dom` established at
the SAME arguments by the parent's Domain plus the code before the call, and the
Err/abort arms match the frozen lines. The NMN_064 four clauses are already
discharged inside 241 by compiled code (NMS_R2Domains.entered, NMS_R2Facts242.successful,
LIBB_ScannerExtent.extent).

Six library, registration and ledger items will block or slow the jobs if not
handled first. One is a genuine registration error (TGB-1). The rest are
caller-dischargeable or bookkeeping.

| Id | Row(s) | Call / field | Class | Fix | Owner |
|---|---|---|---|---|---|
| TGB-1 | 241, and through G1b 240/221/213 | weak `V2Lib.tx2auth` (LIBB_V2Star.weak, LIBB_V2Lib.weak; also NMV_NNCWeak's NNC_WriteFree.law) | (iii) | register the weak law per Env, as the canonical law already is | LIBB_ / NNC_ (G1a); NMV_ re-specialises G2 |
| TGB-2 | 242 | `L.reconstruct q auth scanned.1` (LIBB_PoolReconstruct: `raw auth = none` → panic) | (i) | prove every 233-returned `auth` is in the image of `NND_Carrier.auth` | NMS_ (242) |
| TGB-3 | 233, 242, 241 (all-Args port) | off-`Usize` arms differ by field | port constraint (no spec change) | define the port on non-representable Args by a Ref inhabitant, not a uniform Err/abort rule | NMX_ (233), NMS_ (242/241) |
| TGB-4 | 240 | `Clock::get()` Err conversion (`From<u64>`: `BorshIoError("Unknown".to_string())`) | (iii), low | trust-row sentence, or one `allocIf` arm | lead |
| TGB-5 | 233, 241, 240/221/213 | ledger clauses NKW/NLG-caller `inventory:U16` at 233; NLG-upstream native-input at 241 (".S2") and its `discharged_by` at 240/221/213 | ledger bookkeeping | apply the ledger27 217/234 U16 disposition at 233; cite NMN_064.Domain (four fields) or add a scanner-tag export for ".S2" | next ledger job; NMS_ |
| TGB-6 | 240 (G2) | two weak laws in circulation | coherence | re-state NMV_NNCWeak on the registered weak law after TGB-1 | NMV_ |

## 2. Findings in detail

### TGB-1 (iii): the registered weak 064 law fixes the hash model outside `Env`

Statement. `LIBB_V2Star.weak H d hash world := TAS.lib library (fun _ _ => True)
(NNC_ObservedLaw.w H d hash world)`. `NNC_ObservedLaw.w H d hash world pub proof ck :=
fun _ observed => ∃ pu pr cp, … ∧ NNC_ObservedWeak.Observed H ⟨⟨d,pu,pr,cp,hash⟩,world⟩
observed`. The law ignores its `Env` argument, and `Observed` requires a native run
`NMN_064.Native H s outcome events` with the fixed `H`, and events
`NNC_DigestTrace.render trace` derived from that run.

The consumer. The TAS field (LIB_FullInstances.tas241) and NMS_R2Weak241 /
NMS_R2SiteWeak241 need `TAS.Refines064 V0 I.f064 R0 w`, that is
`∀ x env, Dom064 (lib V0 R0 w) x → w x.1 x.2.1 x.2.2 env (f064 x.1 x.2.1 x.2.2 env)`
(TAS_Interfaces.lean:161; NMS_R2Replay241.VerifyPacket is the same). The SAME `I.f064`
must also satisfy the canonical `Refines064 V0 I.f064 V0.Root0 V0.tx2auth`, whose law
`LIBB_Tx2Auth.law` reads the hash from `Env` through `LIBB_PartitionEnv.H env`
(`env.sha256` on the partitioned input) and `LIBB_PartitionEnv.digest env`.

Why this blocks. At an `env` whose `sha256` differs from the fixed `H` on a queried
input, the actual 064 observation carries `Event.digest parts (env.sha256 parts)`
replies and an exit computed from them. The fixed-`H` law admits only H-derived
replies and exits. So the weak `Refines064` cannot hold for every `env`, and the weak
241 root (G1b), and through it the weak 240/221/213 roots and G2, cannot be
instantiated with the actual implementation. NNC_REMAINING already says the host
f064 must be interpreted "at its actual per-Env digest/error carriers". The
registered V2Lib field does not have that per-Env shape.

Fix (registration only, no RowSpec or domain change). Register the weak law per Env:
`wEnv world pub proof ck := fun env o => NNC_ObservedLaw.w (LIBB_PartitionEnv.H env)
(LIBB_PartitionEnv.digest env) () world pub proof ck env o`. The type is `Bytes → Bytes →
Bytes → Spec (Except verifier.Error Unit)`, with `X = Unit`, which is the instance
LIBB_Tx2Auth.native already uses. Re-prove weak_identity/weak_exact and writeFree at
this law. `accepted_header` then needs its `CheckpointBytes5Inputs.Oracle` premise per
Env (LIBB_PartitionEnv.partition_value is the relevant support). Owner: LIBB_ / NNC_
(G1a). The `world` parameter needs the same check: the canonical `native` quantifies
over `world`, while the weak law fixes one.

Not checked in Lean. If the owner can exhibit `Refines064` for the fixed-`H` weak law
at the actual f064, this finding is withdrawn.

### TGB-2 (i): `reconstruct` panics off the carrier image; 242 must supply the image fact

`LIBB_PoolReconstruct.reconstruct q a c := match LIBB_AuthCarrier.raw a with | none =>
Spec.panic | some raw => …`, where `raw a = some _ ↔ ∃ r, NND_Carrier.auth r = a`. In
RowSpec_242, `auth` is the value returned by `TX2_233.Ref`, which is built from RSL
values: `decodeMaster`/`decodeCheckpoint` (NMX_R2_Carrier images), the 217 transcription
`laneDecode` (RSL lists), and `m.key`/`c.key`/`l.key`. If `raw auth = none` on a reached
path, the Ref admits only an abort there, while the frozen code returns. RowSpec_242
then fails at that input. No lemma establishes the image fact for 233 outputs today.
NNH_ReconstructValuePort takes `a : Raw` as given.

Discharge (no spec change). The fact holds for every 233 return and can be assembled
from existing pieces:
- LIBB_AccountCarriers.master/checkpoint: NMX_R2_Carrier = NND_Carrier on the decoded values.
- NNH_AuthResult.carrier: the image of `NND_Carrier.auth` for given native master/ck/lane.
- 217's `laneDecode` output is in the image of `NND_Carrier.lane`. The frontier has 20
  digests and the root 8 words by `frontierLoop`/`decodeDigestCanonical`, and
  `aspis_core.field.M31 := U32` carries no canonicality. NMX_R3_LaneTotal /
  NND_LaneReturned.value give the native side.

Owner: NMS_ (242), as a step of "install each CLOSED child's full source-site
interpretation". This is the same shape as the TX1 blockers: a library field with a
hidden domain that the caller must establish before the call. Here the caller can
establish it.

### TGB-3: off-representation arms differ by field, which constrains the all-Args port

The RowSpec domains of 233/242/241 are `True`/(D1)/(D2) over unbounded `Bytes` and `Nat`.
The installed laws treat byte lists longer than `Usize.max` differently:
- `LIBB_PoolScan.scanProof`, `LIBB_Tx2Auth.law` (off `Fits`) and `reconstruct` (off the
  image) give `Spec.panic`, i.e. abort.
- `NMX_R2_DecoderLibrary.master/checkpoint` and the request decoder give `none` through
  `fromBytes`, i.e. `Err(InvalidAccountData)` / `Err(InvalidInstructionData)` from the Ref.
- `TX2_217.Ref` is total over every list.

So a port rule of the form "on non-representable Args, return Err" or "on
non-representable Args, abort" contradicts the Ref at some Arg. For example, in 242 an
oversize proof account reaches `scanProof` (abort) after 233 has passed, and 233 never
inspects that account's length. Every Ref here is inhabited at every Arg: the panics are
inhabited, and the only domain-carrying `Spec.call` (Dom064 in 241) is discharged. The
port can therefore be `if representable a then native a else (a chosen Ref observation)`,
with a Ref-inhabitation lemma. No spec change is needed. Owners: NMX_ (233 item 3), NMS_
(242/241). Record the rule so that 242/241 use the same convention as 233.

### TGB-4 (iii, low): the `Clock::get` Err conversion allocates for one reply code

Frozen stage2:479 calls `Clock::get()`. The SDK `get` returns `Err(e.into())` for a
non-SUCCESS syscall code. `From<u64> for ProgramError` maps BORSH_IO_ERROR to
`BorshIoError("Unknown".to_string())` (NMS_SDK_PROGRAM_ERROR.rs.txt:305), which is an
allocation site. RowSpec_240 reads `Env.clock` with no allocation arm. The NMV clock
window (`clock := fun env => ⟨.ret env.clock,[.clock env.clock]⟩`) matches that spec.
RuntimeClockSlotBinding "says nothing about success of the call", so no stated
assumption covers that abort.

This is unreachable in practice: the Agave clock syscall returns SUCCESS or traps.
Fix, one of:
- (a) add to RuntimeClockSlotBinding, or to the ReviewedTranscription-TX2:240 window
  text, that the reply code is never BORSH_IO_ERROR (no target change; lead may add,
  same class as the 2026-11-04 runtime decision);
- (b) add `Spec.allocIf (c = .error (.borshIoError "Unknown"))` after the clock event in
  `TX2_240.Ref` (a RowSpec revision, which needs a ruling).

I recommend (a). Owner: lead.

### TGB-5: ledger clauses that the gate will check at these rows

- 233: `NKW-caller:TX2:233:TX2:216/218:inventory:U16` (OPEN). Its text includes "scan58295
  bytes … reconstruct byte-identical ASF8", which are 242 facts, not 233 facts. Ledger27
  dispositioned the identical U16 clause at 217 and 234 as
  DISCHARGED_IN_COMPLETE_SOURCE_FOLD (NNK_CLAUSE_REVIEW.json). The gate should apply the
  same disposition at 233, with the scan/reconstruct items carried to 242. Otherwise 233
  is blocked by a clause it cannot discharge. Owner: next ledger job.
- 241: `NLG-upstream:TX2:241:TX2:124:native-input` asks for 57607, ≤1880, "inherited .S2"
  and the SAME Reservation. The first two are NMS_R2Domains.entered, and the Reservation
  is the same `env`. ".S2" is not in NMN_064.Domain, which has four fields: proofExtent,
  checkpointExtent, publicBound, root0. So either the discharge cites that the CLOSED 064
  root does not need it, or 241 derives it from the scanner. `scan_proof_buffer` checks
  `bytes[proof_start+8] == Variant::S2.tag()` (r1_pool_adapter.rs:799). However
  LIBB_ScannerExtent exports only the width. If the gate reads ".S2" literally, add a
  `LIBB_ScannerTag`-style export from the SAME scanner observation. Owner: NMS_.
- 240/221/213: the same NLG-upstream ids need `discharged_by` = the 241 root (TCK §3/§5).
  Bookkeeping only. Owner: next ledger job.

### TGB-6 (coherence): two weak laws are in circulation

NMV_NNCWeak.weak240/frame/sdk specialise the weak 240 root at
`NNC_WriteFree.law H digest hash world render`, the earlier renderer law.
LIB_FullInstances/LIBB_V2Star register `NNC_ObservedLaw.w`, the option-B law with no
renderer. NMV_CandidateRoots.root240 is generic in `V`, so nothing is lost. G2's frame
should be restated at the single registered weak law (after TGB-1) so that G1c and G2
use the same `V`. `NNC_ObservedLaw.writeFree` exists for that. Owner: NMV_.

## 3. Clause-by-clause checks that passed

TX2:233 (RSL_TX2_233 vs owned.rs:230-335):
- The order of readonlyBuffer → verifierCheckpoint(v, verifier_program, false) → three
  readonlyAccount → requireDistinct[7] matches lines 246-259.
- The master, checkpoint and lane blocks match: `||` short-circuit before the PDA
  syscall, `map_err` → InvalidAccountData, u64le seed at line 293.
- The 234 call has argument tuple ⟨verifier_program, pool, m, master, r, e, slot⟩
  (= lines 276-284); 234.Domain = True, CLOSED root at LIBB_PoolLib.library/deployed.
- The 217 call is at the SAME `ldata`; 217.Domain = True.
- Box arms: decode_master_box/decode_checkpoint_box after decode, 217's final Box, and
  live_snapshot (318).
- Clone arms on three `data()?` and on `data_len()?` (rev2).
- Arity: `<7` → NotEnoughAccountKeys, `>7` → InvalidArgument.
- Constants: CHECKPOINT_BYTES 1768 = verifier::checkpoint_size(S2) (744 + 16·64), and
  all snapshot sizes 384/192/768/128/256/192/320 match the statement crate.

TX2:242 (vs owned.rs:338-373):
- Length 320 → request decode → profile/release/pool binding (D.pool) → output lane →
  `current_slot?` before 233 (lines 358-364) → `first().ok_or(NotEnoughAccountKeys)` →
  clone arm → scanProof → reconstruct. Error codes are exact.
- decodeRequest/outputLane are total (NMS_R2DecoderImage, LIBB_PoolDecoders.outputLane_source).
- scanProof has only the off-`Usize` arm (TGB-3).
- reconstruct: TGB-2.

TX2:241 (vs owned.rs:417-445):
- Guard ≡ `accounts.len() != 7 || data.get(..4) != Some(MAGIC)`.
- 242 is called at SAME args (Domain True).
- Then `accounts[0].data()?`, `accounts[6].data()?`, checked_add → InvalidAccountData,
  length check, encoder (CLOSED 165, total, by value) → InvalidInstructionData, `!= 1880`
  → InvalidInstructionData, 064 at (public, proof[688..end], checkpoint), then error() =
  format! alloc + one log + InvalidInstructionData (rev2), then emit_result (CLOSED 219,
  total, one returnData event).
- Dom064 at the call: proof 57607 from LIBB_ScannerExtent via NMS_R2Facts242.successful
  plus the length guard; checkpoint 1768 from 233's verifierCheckpoint
  (NMS_R2AuthFacts.checkpoint) plus (D1); public = 1880 ≤ 1880 by the guard; Root0 from
  (D2) at pr.length = 58295. All are compiled (NMS_R2Domains.entered).
- LIBB_Tx2Domain.domain is the literal NMN_064.Domain (LIBB_Tx2Domain.native).
- Weak instance: Dom064(weaken) = the three extents (TCK.dom064_weaken), and 241's
  domain reduces to (D1) (TCK.domain241_weaken, NMS_R2Weak241). The instance shape
  blocks only through TGB-1.

TX2:240 (vs owned.rs:463-481):
- badRoute ≡ line 464.
- set_return_data(&[]) precedes the seven snapshots (lengths = lines 471-477;
  CHECKPOINT_TAIL_BYTES = 1768).
- The Clock event follows the snapshots; `match Clock::get()` → Except.
- 241 is called at (program_id, snapshots in order, data, clock).
- 241.Domain at the call: (D1) from `snapshot` (Ok bytes are stored with length = |data|).
  (D2) comes from (D2′), because acquire/release change only readers/writer/next and
  never `payload`. Compiled as NMV_CandidateRoots.root240 for every V.
- Clock alloc: TGB-4.

TX2:221 / 213 (vs r1_pool_adapter.rs:950-962, lib.rs:56-66, pool_route.rs:3-5):
- Lifecycle 4/5/6 is excluded by (P1) `admitted`.
- stage1Route → S1, else 240; Domain clauses are routed exactly.
- Entry `!admitted` → InvalidInstructionData with unchanged state.
- NNF_Folds.process_tx2/entry_tx2 compile for every V. Note that 221 needs the full
  RowSpec_344 packet as well as 240 (NNK_REMAINING records this), so 221/213 cannot close
  from the TX2 chain alone.

## 4. Not covered

- The native Box/owner association at 233 and the emitted-effects join (NMX items 1-2).
- The A1-A5 physical adapters.
- The actual f064 per-Env interpretation beyond TGB-1.
- G1c, Root0 at the top.
No compile was run, and no counterexample was constructed. TGB-1 is an inspection
argument: the owner should confirm it, or refute it by exhibiting the fixed-`H`
`Refines064`.

Target not yet established.
