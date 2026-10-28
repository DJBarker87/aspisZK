# PDA source specification — Stage 1

Base revision: `0c9b1d3c23b5f22357d2cdac98017df6c0c5466a`.
No frozen implementation is modified. Local source copies and SHA256 pins accompany this report.

The root frozen Cargo.lock pins solana-program **2.3.0** (line 3217,
checksum 98eca145bd3545e2fbb07166e895370576e47a00a7d824e325390d33bf467210),
solana-pubkey **2.4.0** (3349, checksum
9b62adb9c3261a052ca1f999398c388f1daf558a1b492f60a6d9e64857db4ff1),
and solana-sha256-hasher **2.3.0** (3639, checksum
5aa3feb32c28765f6aa1ce8f3feac30936f16c5c3f7eb73d63a5b8f6f8ecdc44).
Pubkey resolves curve25519-dalek **4.1.3**, sha256-hasher resolves sha2 **0.10.9**.
The generated-final FunsExternal_Template line 436 declares the corresponding
Pubkey.create_program_address as an external axiom; it is not imported here.

## Reached source and runtime split

Frozen extraction/native-sources/r1_pool_adapter_owned.rs lines 265–317
calls create_program_address for master, checkpoint, lane. Immutable registry
branch lines 112–165 calls it four more times: registry, registry programdata,
entry, verifier programdata. All SDK errors map to ProgramError::InvalidAccountData.
The matching borrowed source is r1_pool_adapter.rs lines 553–608, 706–758.
`JHj_Authentication.source` has three direct PDA premises and a registry premise
containing four calls: **seven calls total**, not four. The two legacy registry
calls at owned lines 180/203 are on the other policy branch and are excluded.

solana-pubkey-2.4.0.rs lines 911–963 implements the SDK function. Before either
platform branch, >16 seeds OR any seed >32 bytes returns MaxSeedLengthExceeded;
empty seed lists/empty seeds are permitted. No extra delimiter, length prefix,
bump search or implicit bump occurs. A supplied bump is an ordinary final seed.

On target_os=solana it calls sol_create_program_address with slice descriptor
pointer, count, program-id pointer, and writable 32-byte output. Code 0 means
success; nonzero uses PubkeyError::from(u64) (lines 128–137): 1 InvalidSeeds,
2 IllegalOwner, other nonzero panic. Numeric 0 in that conversion denotes
MaxSeedLengthExceeded but is intercepted as SUCCESS in this wrapper.
Compute exhaustion, invalid VM memory and syscall traps are runtime admission
conditions, not returned PubkeyError values.

On the host, Hasher::default is incrementally updated for each seed, then
program_id.as_ref() and the 21 ASCII bytes `ProgramDerivedAddress` (marker line
55). The hash input is exactly `seeds.flatten ++ program_id ++ marker`.
solana-sha256-hasher-2.3.0.rs lines 7–27 use sha2::Sha256 update/finalize;
this host fallback does NOT call sol_sha256. The separate hashv wrapper does
call sol_sha256 on Solana, but that is not the SDK PDA branch.

The host fallback calls bytes_are_curve_point(hash), lines 456–468:
CompressedEdwardsY::from_slice then decompress().is_some(). Success returns
Pubkey::from(hash.to_bytes()); curve success rejects with InvalidSeeds.
This is compressed Edwards-Y decompression, not signature validation, subgroup
membership or torsion-freeness. No canonical-encoding restriction should be
silently added. The 32-byte compressed sign bit does not change existence of a
square root; the low 255-bit Y is reduced in the field. The mathematical model
uses the twisted-Edwards equation and an explicitly retained correspondence
obligation to dalek's actual decompressor. No dalek equivalence is claimed proved.

## Model and certificate boundary

JHs_PDA.derive uses the existing JFp_SHADigest.digest, guarded by seed limits,
then the mathematical OnCurve predicate. SHA values may be rewritten only by
named per-call digest equations. Each expected output requires its own named
OffCurve fact; there is no successful-op38 certificate field. The runtime
syscall/model correspondence is not supplied by an opaque external SDK axiom.
The mathematical guard/error theorems do not establish runtime equivalence.
