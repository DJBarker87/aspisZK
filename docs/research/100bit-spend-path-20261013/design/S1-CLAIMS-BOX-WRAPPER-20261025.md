# S1 Claims Box boundary: actual pointer coupling and remaining union obstruction

2026-10-25. **S1/S6 remain OPEN; no enclosing source/SDK premise removed.** The previous raw-loop initialization packet `1b94856af9` remains valid at its explicit allocated/raw/normal-row domain. This packet tests the actual Box operations around that loop and narrows the remaining obstruction. No frozen Rust source, candidate adoption, security target, another track or another worktree is changed.

## New native pointer/ownership result

`claims_box_wrapper::box_projection_transfer` uses the full frozen native QM31/CM31/M31, Row29 and Claims3 types, with all348 raw words symbolic. Core field source and all88 native dependency source pins remain at freeze25866ec331cc7ce27dd9956609c11d32fa8fa58a. A real raw allocation starts without a zero fill; real `Box::from_raw` constructs Box<MaybeUninit<Claims>>, the actual `.as_mut_ptr()` supplies the store base, the exact original pointer-cast/add/write loop runs on the corresponding symbolic rows, and real `.assume_init()` produces Box<Claims>. Both base pointer and returned owner pointer are asserted equal to the allocation address. An arbitrary one of all87 cells has the exact four expected words; first/last-cell covers pass. The returned owner is actually dropped.

This is a **DEFAULT-check pointer/value/ownership-control result**, NOT an initialization proof. No `-Z uninit-checks` result is attributed to it. It is not a whole frozen Claims check: the fallible heap constructor and interleaved decoder/error return are not this harness's functions. There are no stubs or `kani::assume`; symbolic predecoded rows are explicit inputs. Kani's normal allocation-success model is retained; allocator failure, target SDK state, abort/effects and deployed SBF association are open. Pointer identity is not promoted into whole heap/effect equality.

v1 codegen: exit0,0.455338417s,RSS140230656B,observed aggregate19267584B,swap0. v2 verification: exit0,5.369578417s,RSS728498176B,aggregate754827264B,swap0; 0/153 failed,2/2 covers,solver4.9451904s. Kani0.67.0/rustc1.93.0-nightly53732d5e0 on Apple Silicon, optimized/overflow-checked Rust, unwind32/unwinding assertions, one job and shared atomic lock. All exact source/tool/sysroot/commands/pre-post hashes are retained. Ordinary focused Mac guard2GiB/180s/64 processes, no watchdog or heavy job. `#print axioms` is N/A.

## Actual compiled helper inventory

Read-only `goto-instrument --show-goto-functions` on the actual linked wrapper artifact produces source text. The exact MaybeUninit::as_mut_ptr body has two pointer locals, `address_of(*argument)`, a pointer cast and return; it has no payload value load or call. `audit-ir.py` checks that exact instruction shape with reversible local-name aliases.

The complete transitive call inventory of as_mut_ptr and Box::assume_init contains22 actual helper bodies, with no missing callees and no allocation/reallocation/deallocation call in that closure. Bodies include the real into_raw_with_allocator/from_raw_in/Unique/NonNull/ManuallyDrop paths and source locations. The latter closure is **inventoried, not a proved alias/heap/read-footprint theorem**. It contains loads of Box pointer metadata and the zero-sized Global allocator. This syntax inventory is not itself compiler correctness, native initialization, a full Rust semantic refinement, or a release artifact proof. Automatically inserted GOTO ASSERT/ASSUME instruction pairs are upstream checking instrumentation, not added harness assumptions or custom Lean axioms.

IR-v1 failed in Python preexec before the tool launched; its input/failure are retained. IR-v2 ran successfully but selected the symbol-only artifact and produced no function bodies; it receives no footprint credit. Its contemporaneous controller pin is matched by an explicitly labeled reconstruction, not called a snapshot. IR-v3 selects the linked artifact: exit0,0.128011s,time-v RSS13500416B,swap0,1015309 bytes of source text. Exact input artifact/tool/controller hashes and unchanged checks are retained; no binary artifact is committed. The ordinary read-only guard was2GiB/20s/64 processes/8MiB output, with no watchdog. No compiler or SAT replay was used to collect it.

## New failure: real partial-prefix cleanup

A separate target, `claims_box_wrapper::drop_partial_uninitialized_box`, DOES retain `-Z uninit-checks`. It allocates real raw Claims storage, constructs the actual Box<MaybeUninit<Claims>>, writes a symbolic prefix of0/1/2/3 rows using the retained raw base, and calls the real Box destructor. This avoids the previously unsupported as_mut_ptr call and tests cleanup directly.

v3 codegen: exit0,0.450141458s,RSS147111936B,aggregate14729216B,swap0. v4 verification: exit1,11.024355166s,RSS1112899584B,aggregate1112080384B,swap0;1/142 failed,0/4 covers. The failure is “Interaction between raw pointers and unions is not yet supported” at `core::ptr::drop_in_place::<Box<MaybeUninit<Claims>>>`. No memory/time/watchdog cap was reached. This is a tool obstruction, not a demonstrated program bug or cleanup proof. No higher-cap or unchanged retry was attempted. Nonfailing checks are not credited as a successful partial-cleanup proof.

The historically copied expected-time caption in v1/v2 mentioned raw initialization; the exact commands/kind/selected target establish DEFAULT scope and are preserved. Future runner captions distinguish the partial-drop UNINIT check. No old result is relabeled.

## Consequences and remaining obligation

The raw-store loop has separate native uninit-enabled evidence, and the actual Box wrapper now has pointer/value coupling plus a finite exact source-body inventory. They have NOT been composed into a supported native initialization/cleanup theorem for the full original function. The needed composition must justify the metadata-only wrapper operations and actual allocation/decoder/error/drop/effect boundaries in a common semantics; an abstract Boolean or opaque initialized Box cannot supply it. A fully validated source route would still require an explicit adoption decision and caller/CU/artifact re-pins. Safe Claims remains unadopted.

The research branch's separate Claims-parent-to-finish result and its SDK import repair remain with that owner; this packet does not duplicate or modify them. Terminal/source primitive installation and original S1/S6 caller/release joins remain open. The next useful action is a supported wrapper/cleanup semantic transport or another unclosed concrete S1 boundary, not more RAM or the same whole initialization replay.

Read-only source-only check: `python3 tools/s1-claims-box-wrapper-20261025/check.py`. No new Lean source or axioms, no deployed verifier changes, no source-only packet binaries. The implementation-linked <=2^-100 per-attempt target remains NOT ESTABLISHED.
