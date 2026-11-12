# Aspis trust inventory additions (Stream A lead, 2026-11-12)

Status: rows for the Aspis pin, added by the lead under the owner's decisions of 2026-11-04 (runtime class), 2026-11-10 (only std/SDK/runtime items may be rows) and 2026-11-12 (account write boundary: SDK/std rows instantiated at listed call sites, carried as named hypotheses). Nothing proved; target not yet established. Instantiation lists cite the on-chain workers' records (future-version 8c7fec164cf, evidence/aspis-extraction-20261112/onchain/README-stage2b.md). The Pool program's list is pending and will be appended.

## Row: AccountWriteBoundary (instantiation of S2TrustedSdkBorrow + TrustedStd, carried by RuntimePersistence)

Class: SDK/std rows at listed call sites. Not an Aspis trust row: each listed function's body is one SDK borrow and one assignment or fill, no arithmetic, no branch on data, no read; the grammar check (Pool worker's tool, planted negatives) is the evidence that this is a fact. Carried as a named hypothesis in the trust-inventory structure of the top theorem; never a Lean `axiom`.

Contract shape (per call): after the call, the account's data equals the old data with the stated bytes at the stated offset (or the stated fill), or its lamports equal the stated value; every other field of that account and every other account are unchanged; a failed borrow is an error return with nothing changed.

Instantiations, verifier program (programs/r1-cost-probe/src/r1_pool_adapter.rs at aspis-next 8ba85f1946b):
| function | lines | operation | contract | callers | order |
|---|---|---|---|---|---|
| write_zero_data(account) | 5 | try_borrow_mut_data; data.fill(0) | data := all zero bytes, same length; else unchanged | close_checkpoint (line 1053) | 1st write |
| write_lamports(account, lamports) | 5 | try_borrow_mut_lamports; **handle = lamports | lamports := v | close_checkpoint (lines 1054, 1055) | 2nd, 3rd writes |

Grammar note: write_zero_data's written value is the literal 0 over the whole slice (a constant fill, not a parameter). Accepted as a grammar case "fill with a literal over the whole borrowed slice"; `<[u8]>::fill` cannot panic. The sum written by the third call is computed before any write with the frozen overflow check, in translated code.

Gates recorded by the worker: write-route gate over the LLBC (no other call of a mutable handle), bodiless-Aspis gate (exactly these two), no account read after the first write, frozen write order, differential test on 240 cases comparing complete data and lamports of every account including rejections. Owed: the grammar checker run with planted negatives (tool not yet committed); the devnet rejection case.

## Row: RuntimeSha256Value (existing; realisation updated for Aspis)

SolanaDigest::digest_into is the only target_os site reached from the entry (target-os.tsv, 78 sites in four crates). SBF realisation: the sol_sha256 syscall called directly (three lines, the only unsafe block); host realisation: solana_sha256_hasher::hashv. Both realise H; the reply value is trusted as SHA-256 of the ordered request slices. Conditions: the call site passes the write-boundary grammar check (one syscall, slices and output buffer are parameters, no logic); the fidelity run compares every Merkle parent and transcript digest host against SBF on the recorded transcripts.

## Row: CoreIteratorAny (new, same class as CoreSliceIteratorModel HM-B)

Iterator::any over core::slice::ChunksExact<'_, u8> (merkle_verdict: chunks_exact(8).any). Semantics: the Rust core library at the extraction toolchain, for this instantiation. Kept as a bodiless external because every rewrite adds a check per element. Discharge: the Aeneas library definition of 0d21a9ec if it has one (X3's probe table decides), else the row stays with the exact call site.

## Row: CoreArraySliceOps (existing HM-D; member confirmed)

core::array::map at eleven sites (several in the Poseidon evaluation). Already a member of HM-D ("Array::map, slice/array PartialEq, slice windows, slice first, RangeFull"); the eleven call sites are listed in std-external-callers.tsv. Same discharge route as above.

## Constants

Program ids and the loader id are emitted as calls that compute the value. Rule "constants by value, checked by hash": the manifest carries the evaluated value from the build, and the fidelity run checks the emitted computation reproduces it.

## Compute

Rewrite round against the frozen program on the two recorded payments: +1,234 CU each (+0.10 percent), all from expand_values (one added range check per value). Within the round gate (soft stop at 1 percent on the heaviest worst case, 5 percent per function). The ELFs carry no function symbols, so the per-function delta is the per-item instruction count from the measurement build plus replays, not a symbol-level diff; the gate reads that as the measure.

## Externals re-classed against the native-library emission (8c7fec164cf)

Rule (zk-73, agreed): against the Aeneas 0d21a9ec library, the generated external template declares as axioms exactly what the library does not define; every other std item the emission uses is a library definition and leaves the trust list. Result for the verifier program (ASPIS-EXTERNALS-TRUST-MAP-20261112-r2.tsv): 23 std items remain external and keep rows (HM-B members: array IntoIter into_iter/next; HM-C members: Option branch/copied, Result clone/unwrap_or_else; HM-D members: array map, array eq/ne, slice first/starts_with; CoreIteratorAny: Iterator::any, slice Iter::any; TrustedStd: black_box, Range clone, str::as_bytes, str::from_utf8 (new member), error/iterator types; allocator: Vec try_reserve_exact/into_boxed_slice; S2TrustedSdkBorrow: RefCell/Ref/Rc and Ref::deref). Gone after the rewrite round: Rev<I>::fold, alloc::fmt::format with String::deref. The X1-era items not in this list (Iterator::fold variants, ChunksExactMut, RangeInclusive, Option and_then/eq, Result is_err, array IntoIter fold, Box try_from, chunks_exact_mut) are now library definitions of 0d21a9ec and are no longer trust items. Two items new since the rewrite need their use named: core::str::from_utf8 in close_checkpoint (line 1039) and str::as_bytes in program_id (the constant-by-value computation).

## Named uses (from the source at aspis-next 8ba85f1946b; both present in the frozen text, visible now because close_checkpoint translates)

- core::str::from_utf8, close_checkpoint (r1_pool_adapter.rs 1042-1043; frozen 1042): decodes the checkpoint account's derivation seed from the close instruction's data[2..] after pool_route::is_close_checkpoint; on the ACCEPT path of the close instruction (rent recovery, not payment acceptance); result passed to Pubkey::create_with_seed(base.key, seed, program_id), which must equal the checkpoint key. Row TrustedStd member str::from_utf8 with a two-directional contract: Ok with a str whose bytes are exactly the input when the input is valid UTF-8, Err otherwise (mapped to InvalidInstructionData before any write). The account-to-base binding rests on create_with_seed (SDK/runtime row: hash of base key, seed bytes, owner; rejects seeds over 32 bytes inside the SDK item) plus this byte identity. The payment verification path does not call from_utf8.
- str::as_bytes, deployment_ids::program_id (deployment_ids.rs 55): compile-time decoding of the two program identifiers from the build environment strings; constant by value; the manifest carries the evaluated values and the fidelity run checks the emitted computation reproduces them. Not on any run-time path.
