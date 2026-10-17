# Actual prepared sum-of-three loop proofs

This graph proves checked execution of the actual three-channel loop and three-component loop used by the prepared QM31 sum-of-three source cut. It preserves unchanged cells and derives the checked reads, writes, casts, multiplication and accumulation bounds. The per-index right-component constructor is also proved successful and canonical from canonical actual right inputs. Existing range-iterator, M31/CM31 addition and prepared-state proofs are reused.

The complete outer three-input accumulation, channel-sum conversion and packed Poseidon family theorem remain open. Component-loop theorems retain their stated input bounds and source-read premises; this checkpoint does not pretend these already establish the entire caller. No independently assumed output-model equality is claimed as source correspondence.

`check_source.py` compares the six source helper/loop declarations against the sealed indexed Funs candidate, plus its closure type from Types. Only whitespace is normalized. The source namespace/imports reuse existing nominal field/prepared owners. This checks the isolated declaration bodies, not preservation of the current Rust caller through extraction and runtime.

Sixteen focused targets passed, with sixteen exported reports containing only standard axioms, peak RSS at most 2,976,468 KiB and zero swap. Each receipt retains its actual module target, command, source/cache revision, direct-import/object/source hashes, elapsed time and resource reservation. Source-only target has no report. Internal graph object pins were checked before publishing. There was no package-wide replay.

Earlier failed monolithic loop attempts and the live resource adjustment are retained under diagnostics. One stopped run raised MemoryHigh from 4 to 5 GiB while keeping MemoryMax 6 GiB and swap disabled, then stopped at exit 143; its peak process RSS report was 7,966,572 KiB and no output was produced. The successful replacement factors nested updates and pure frame invariants into small symbolic lemmas. It was checked under the original 4/6 GiB scope without raising caps. The failed run is not release evidence.

Final accepted-spend soundness, privacy, current-source/runtime correspondence and the deployed artifact remain open.
