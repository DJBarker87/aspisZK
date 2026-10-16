# Worker A: actual begin and local transcript checkpoint

Producing revision: `c16ab4d76619cf2cf80ece9d7e60e47975957af0`, based on accepted rebase `ebe378259fb7d9c8a007eec2c8a8eb4850e549fc`. The sole production change is the authorized ten-call begin unroll. No SBF was built. B's four native acceptance gates are separate evidence.

| Focused target | Exit | Wall s | Peak RSS KiB | Swap | Axioms reports |
|---|---:|---:|---:|---:|---:|
| ExtractedDigest32Transcript, named carrier | 0 | 1.875 | 2662096 | 0 | 5 |
| ExtractedDigest32Callers, named carrier | 0 | 1.894 | 2662020 | 0 | 11 |
| ExtractedDigest32Begin | 0 | 7.709 | 2775376 | 0 | 4 |
| ExtractedDigest32SamplerTransport | 0 | 2.288 | 3860820 | 0 | 9 |

All 29 reports contain only the standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`, or no axioms. Exact commands, source/tool/runtime hashes, cgroup limits, logs, failed/stopped attempts and producing objects are inside the archive; the manifest indexes every byte. Limits were MemoryHigh=6 GiB, MemoryMax=8 GiB, MemorySwapMax=0. The worker stopped its own process on externally arriving Lean jobs and did not stop the external jobs.

`begin_success` derives all fifteen actual `validated_record` and `semantic_validated` calls in row order from actual `begin` success. It identifies their results with the returned `lambda`, `chi`, `theta`, ten `zc` values, `mu`, and `eta`. `SemanticRun.carry` derives hash and next-row carry. `semantic_step_success` gives each accepted semantic row's exact absorb/read1/read2 calls and sampler success. The opening results prove the actual `Transcript::new`, `absorb`, and `block` equations, including reseeding from the supplied semantic state. The sampler transport proves the current extracted sampler equals the accepted index sampler under the four-coordinate nominal map, then reuses its unconditional totality/canonicality, rank coordinates, and current QM31 decoder equality.

The coherent carrier is named Types `34d88375…` and Funs `e98bb123…`, freshly checked by C. The complete original-declaration audit (79 unchanged original declarations, exact token hashes) and producing Type/Fun receipts are archived. No raw/new Types and stale Funs cache are mixed.

The extraction kit contains 52 exact source cuts, pinned byte spans and a deterministic `extract.py --check`. Its current LLBC has `has_errors=false`; Charon exit 0, 0.4055 s, RSS 212732 KiB, swap 0; Aeneas exit 0, 8.8165 s, RSS 1262716 KiB, swap 0. Both source and generated evidence are included.

Remaining scope is explicit: rows 15–32 through the actual verifier and `Prepared::new`, the row-26 caller bridge, actual `hbytes`, `semChalsZ_read.hread`, `htyped`/`ha`, C2 provenance, and the full source-to-literal transcript correspondence are not established by this checkpoint. The local opening constructor theorem does not assert actual `Prepared::new` reachability. C is independently pursuing focused whole-body caller cuts. The full-native diagnostic LLBCs have `has_errors=true` (known Iterator trait-clause failures) and were rejected without Aeneas. The subset inventory draft is not the full release inventory; B owns its merged successor.

An evidence defect is retained: the initial pre-unroll runner reused one LLBC filename and the noncovering root-b probe overwrote the original root-a blob. The original hash/logs remain. Repeating the exact original command on its unchanged source produced a valid (`has_errors=false`) but differently hashed LLBC; the original blob and its `has_errors` value are unavailable. This is not claimed as a byte-identical restoration. Eight early overwritten staging manifests were reconstructed from retained source snapshots and accepted only after matching their exact recorded SHA-256 hashes. Later attempts snapshot manifests automatically.

Run `python3 verify.py` for read/hash-only verification. This does not compile Lean or run runtime tests.
