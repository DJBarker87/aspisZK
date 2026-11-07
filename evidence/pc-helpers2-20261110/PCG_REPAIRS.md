# PCG own-input repairs and exclusions

Shared launchers, reservation, shim, host workspaces and tool binaries are unchanged. All repair work is on PCG-owned sources and client validators.

- Initial frozen-source serialization encountered one binary fixture; changed the input container to base64 bytes before any host/proof launch. Frozen source bytes remain exact.
- SDK K001/005/006/007/018: compile-only input failures listed in PCG_STAGE1_NOTES.md. The private SDK compiler wrapper supplies only the already-frozen deployed target edge and pins source checksums. No dependency drift or registry edit.
- Source audit L003 assumed a .cargo-checksum.json file existed in the retained registry. It did not. L004 instead validates source bytes against the package archive whose complete SHA256 equals the frozen Cargo.lock checksum: a stricter replacement, passing four rejecting source mutations.
- K030: generated request reference had an extra closing brace; fixed the generator and reference. K032: compiling without the private SDK dependency search path could not load the retained solana_program metadata. K033 supplies the same package wrapper/search path, passes. No semantic verdict was changed by renaming a harness.
- L017 is excluded introspection: Slice is a subtype, with no Slice.mk declaration. Its other prints supplied the needed actual type/array semantics. No theorem was introduced there.
- L018 is excluded: `matches` is a reserved Lean token. The legal name stored_result in L020 has the unchanged intended statement; all request/domain laws passed. This is a parser fix, not a renamed native verdict.
- L019 is excluded: decide cannot normalize Aeneas's opaque target Usize.max. L021 uses scalar_tac's existing architecture bounds; no new hypothesis. Its five final roots print standard axioms only. Failed elaboration's sorryAx summaries confer no credit and are excluded from all selected objects/roots.
- K008 ran no Kani: the native statement manifest rejected root-Pool feature spellings. K052 and all subsequent statement tasks use the exact resolved deployed aspis-statement feature list (PCG_STATEMENT_DEPLOYED_FEATURES.json). Every all-crate graph/lock check is retained.
- L022 is excluded: nativeStored depends on a noncomputable seed-domain decision. L023 marks that model definition noncomputable; statements unchanged, standard axioms.
- K009 was an intended corrupted-arm assertion failure. The client initially expected a literal assertion message; assert_eq emits Kani's runtime-format placeholder at core::panicking::assert_failed_inner. PCG_queue.py now accepts that exact assertion category, requires FAILED and exit1, and rejects unwinding failures. No proof replay was launched for this parser correction.
- E001 timed out after180s during full Pool dependency compilation (scope memory peak1274900480 bytes; /usr/bin/time RSS78104KiB at timeout does not purport to be aggregate child RSS). No reference emitted and no credit. The shape is retired, not rerun. E005 isolates the same two constant conversion expressions with byte-copied full enum carriers in a dependency-free reference; it passes with NCO pins, retaining all26 ProgramError variants and String.
- L024 is excluded: eight local-let index equations did not rewrite the expanded byte source. L025 explicitly unfolds only that local byte-array abbreviation in the equations. No scalar/byte-domain hypothesis is added.
- K055 failed before verification because the independent canonical-step module omitted its M31 import. The import is fixed for K063; the owned-window function retains its original name and property. No timeout/memory-killed shape was retried.

New modules only; generated Aeneas options are retained verbatim. No source sorry/axiom/admit/native_decide, added maxRecDepth/maxHeartbeats, production-source edit, ELF rebuild, key/fund operation or push.

PCG_K082/090/091 selected no SDK harness: own later lib upload gated it on PCG_SDK_NATIVE; repaired task flag (no proof verdict). Keep exact original full names for suite.

Own runner dependency closure now recursively uploads referenced PCG_ harness files and retains its missing-dependency assertion; K086 refused before launch, no scope consumed.
