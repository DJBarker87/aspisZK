# D581 adopted entry interpretation

Evidence class: **binary-structural (adopted binary), plus V370 compiler-cohort**.
This is not a machine proof of compiler correctness or a new T field.
Binary SHA-256: `da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0`.
The adopted build is revision `4ea2abfcc3a50f1b6e766ed41ff07cf815085a87`,
`devnet_spend`, rustc 1.94.1, x86_64-unknown-linux-gnu, client profile opt-level 3,
panic abort, features r1p-check and aspis-r1-cost-probe/ct-host-prover,
getrandom_backend="linux_raw". Exact recipe, dependency features and profile
remain pinned in adopted-backend-confirmation.json and entry-frame-binding-D572.json.
No client execution, request submission, wallet creation or key operation occurred.

## Entry and source correspondence

`out-N91601.log` contains the complete selected functions and static references;
`binary-correspondence-D581.json` pins their bytes, analysis tools and adopted
source files. GNU objdump/nm/readelf 2.42 tool executable hashes are recorded.
Addresses below are ELF virtual PCs; for PIE execution add the actual load bias.
Stack addresses are actual runtime addresses, never ELF addresses or invented bases.

| Source prefix component | Adopted binary correspondence |
|---|---|
| Client `plan::prove`, source call to `RealR1_client::prove_for_proof_accounts` | Adapter and S2 wrapper have no separate named symbols. Their specialized call is in `plan::prove` (0x4f350), at 0x527b5 to retry_attempt 0x5c990. Association uses the pinned source plus V370, not absence of symbols alone. |
| Actual entry arguments | 0x5278c Result destination, 0x52794 public argument, 0x5279c compiled argument, r8 hash, 0x527a4 nonce store; ecx=1 selects S2. Stack pushes carry callback capture and initial k=0. All are reached arguments, not freely chosen model data. |
| `retry_attempt`, k < ATTEMPT_CAP | Six pushes and sub rsp,0x108 at 0x5c99a; k in rbp, cmp 7 at 0x5c9ac, larger k returns AttemptsExhausted. Rejected attempt recurses at 0x5cb20, carrying incremented k/capture/store. |
| Supplied callback `accounts.nonce(k)` | Inlined at 0x5c9bb..0x5ca02: capture dereference into rdx; compare k to entered at +0x100, failure branch 0x5cb91; load keys[k] using k<<5 at 0x5c9ec/0x5c9f0; store entered=k+1 at 0x5ca02. No independent callback frame. |
| Callback mask argument and helper Result | Let c be retry post-prologue rsp. Mask loads/stores at c+[16,48); Result pointer c+64 at 0x5ca09; rsi=c+16 at 0x5ca0e. Call 0x5ca13 through GOT 0x1e80a0, whose RELATIVE relocation is 0x1457a0. |
| `generate_for_mask_nonce` mask guard | Entry 0x1457a0, six pushes then sub rsp,232 at 0x1457aa. rbx holds incoming Result pointer, r14 incoming mask pointer after nonzero guard. Zero mask branches 0x1457d2 to error, never reaches initializer. |
| Reached original loop body | First initializer PC 0x1457ef; rbp=retry starts at zero (0x1457e0). Backedge increments at 0x1458e1, compares to 16, and branches to 0x1457ef at 0x1458f1. Exhausted limit returns error. Prefix includes only reached retry<16, with no future-success condition. |
| original64 initializer | Four zero SIMD stores at 0x1457ef,0x1457f5,0x1457fb,0x145801. This is before the first syscall, not before function prologue. |

Let `sp` be entropy post-prologue rsp, so **sp=c-240** under nonwrapping
ordinary call-stack arithmetic (8-byte return address, 48-byte saved registers,
232-byte reservation). Therefore incoming mask=c+16=sp+256 and helper Result
base=c+64=sp+304. They are outside the entropy reservation. Success writes
97 initialized Result bytes, ending at sp+401=c+161, inside retry's reservation.
This does not infer the complete Rust Result allocation extent or padding from
its initialized stores. Retry's temporary later stack adjustment at 0x5cab6 is
AFTER the entropy call; it must not be used to compute this call's c.
Plan reserves 0x52a8 bytes after six pushes, using five 0x1000 page probes and
one 0x2a8 subtraction. Page probes do not establish all subsequent permissions.

## Secret-byte and copy table

Intervals are half-open, relative to that same sp. Storage is phase-sensitive.
Before initializer, original64 is not a new initialized owner; repeated numeric
addresses on retry do not identify the same source lifetime.

| Source storage / role | Machine bytes | Writes / copies |
|---|---|---|
| Original Zeroizing 64 | [0,64) | Initializer above; getrandom syscall 0x145817 requests rdi=sp,rsi=64,rdx=0,rax=318; positive partials advance pointer/reduce size, EINTR repeats. |
| field_mask_entropy | [64,96) | Original first half via xmm2/xmm3, stores 0x14584b/0x145851. Source zero initialization is elided before complete overwrite (V370). |
| leaf_salt_seed | [96,128) | Original second half via xmm0/xmm1, stores 0x145862/0x145868. Same initializer caveat. |
| Return mask staging | [128,160) | Input loads xmm4/xmm5, stores 0x1459a1/0x1459a9. |
| Return field staging | [160,192) | Reload original into xmm0/xmm1, stores 0x145968/0x145971. |
| Return seed staging | [192,224) | Reload original second half into xmm2/xmm3, stores 0x145985/0x14598e. |
| Remaining reservation | [224,232) | No secret store identified; subtraction alone does not prove mapped writability. |
| Caller mask copy | sp+[256,288) | Callback's two SIMD stores into retry frame. |
| Returned tag/mask/field/seed | result+[0,1),[1,33),[33,65),[65,97) | Six interleaved stores 0x1459b2..0x1459ca, then Ok tag 0x1459cf. |

Reject cleanup calls the 32-byte zeroize at 0x144ac0 on seed then field
(0x1458c0/0x1458c8). That function has 32 explicit byte-zero stores at offsets
0..31. Original64 is cleared by the byte loop at 0x1458d0..0x1458df.
Error and success share original64 cleanup at 0x145930..0x14593f. Return staging,
caller mask, moved-from inner copies and XMM contents are not erased by that
loop. No claim of register erasure or total L3 sanitization follows. Compiler
barriers are source/compiler ordering obligations; no hardware fence is inferred
from them. All these storage channels must remain in the L3 interpretation.

## ActualEntropyEntryPrefix correspondence and remaining boundary

Keep EXACTLY the four binders of BLOCKER-D580 (reproduced in BLOCKER-D581).
The intended fixed domain is finite executions of the adopted proof-account
entry paired with its source execution at
`opsNative (rawBase base) heap box ops`, stopping with relocated RIP=0x1457ef,
after the mask and retry guards. It includes every reached retry and every
prefix with subsequent rejection, error, fault, or exhaustion. Pairing must
preserve entry arguments, callback state and all preceding world answers and
events. Membership must not require `actual_frame_entry` or eventual success.

This paragraph specifies the correspondence domain; it is NOT an implemented
Lean type or an inhabitance proof. Existing `World` has no RIP/rsp/mappings,
process memory, ownership interpretation, or machine reachability relation.
Disassembly does not add those carriers to it.

For a real member q: sp(q) is its machine rsp, memory is THAT process's memory,
writable(q) is THAT mapping's writable-address predicate, owner(q) identifies
THAT activation, and state(q)'s existing heap/live keys must be the owners in
THAT execution. The binary table fixes slot addresses and initialization
phases; it does not supply the absent global owner-to-process correspondence.
No arbitrary total memory function, empty heap, or handpicked fresh address
has been introduced.

Use of the structural interpretation: substituting this actual sp in existing
EntropyDeployedLayout identifies original/field/seed at sp,sp+64,sp+96;
`separation` gives their pairwise numeric separation. Under the STILL REQUIRED
frame-entry conclusion, `address_bounds` uses its nonwrap conjunct,
`heap_frames` its heap conjunct, `live_frames` its live conjunct, and
`original_admission` the last two. This is a precise conditional use of existing
checked laws, not an application to a constructed actual q or a new proof.

Under SysV entry alignment (rsp mod16=8), six pushes plus sub232 give sp mod16=0.
That conditional arithmetic is structurally established. Neither every byte of
232 being mapped writable nor exclusion of every existing abstract heap/live
owner follows from instruction decoding. Those remain FRAME-ENTRY runtime P;
compiler/source pairing, ABI validity and physical ownership preservation remain
V370/L3 residuals under l3-1. No residual is silently added to T.
