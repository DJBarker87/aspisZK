# Resume 2026-10-27

Baseline c35956a836; Env-J 43000–43299, new 100 Lean / 8 Kani budget, last three charged Lean attempts reserved for bundle audits. Prior tally retained as TALLY-prior.json. Source laws 4 → 5 (V179/op28 added, P6); canonical endpoint premises removed: 0. Target not yet established.

op26: split no-stub gate resume-join-one-byte-01 passes base/suffix lengths 0–1, arbitrary bytes/index. Owned return extraction retains structured Drop failure. Mutable-reference extraction also rejects escaping reference outputs (aeneas-source-join-mut-opt-resume-01). No row credit.

op28: owned identity String reference extracts without callbacks or Drop. Lean 43000/43001/43004/43005 accepted; 43002/43003 rejected, no failed proof artifact accepted. P6 native gate resume-string-path-01 passes all valid UTF-8 length-2 strings, arbitrary byte index, exact content/length; no deployed-toolchain association inferred. Stable bundle op28_source uses StringTypes/selectedString; prior names remain unchanged. The four previous laws remain available on selectedAll; inherited selectedString preservation checks at 43008 failed on an unclosed section; corrected source accepted at 43009.

op30: native content/capacity gate resume-string-capacity-01 passes n≤4. Direct optimized extraction hits Aeneas Z.Overflow; owned reference calls unresolved alloc.string.String.new. This is not a closed source law. Capacity/allocator effects not erased from native evidence. op32 retains its exact NATIVE-EFFECTS.md deferral.

All new native/extraction runs have collected-receipt.json; numbered Lean receipts include full target, exit, wall, RSS, swap, revision and axioms. Kani gates are small control/index checks only. No SHA Kani run is permitted or performed in this resume.


After op30: including String.new produced has_errors=true despite Charon exit 0 (unsupported ConstEvalVal / dangling zero-allocation pointer during constant conversion); Aeneas was correctly not launched. This is a translation failure, not a checked Rust execution or ROW counterexample.

op31: optimized exact push_str extraction reaches the escaping-reference preflight; native split gate resume-string-push-r01 passes valid UTF-8 two-byte source plus one-byte suffix, full length and arbitrary output index. No source law credited.


op33: retained-owned adapter avoids abandoning the input, but its exact extraction still rejects structured Drop (aeneas-source-op33-retain-opt-resume-pop-retain-01). Loop-free error-empty/singleton gate resume-pop-errors-r01 passes every Error variant. No generic pop row credit.

SHA: direct private helper start-from diagnostics emitted empty function modules; these are not accepted extractions and confer no source credit. The full dispatcher does have a nonempty exact body but fails loan preflight. A byte-matched owned fallback helper module now extracts the scalar two-round function without callbacks, accepted at 43010; schedule port exposed a signed-shift RHS backend type mismatch, rejected at 43011. The reference now explicitly types the literal shift 10 as u32 (same positive bit count); that port is documented in fallback-reference-source-map.json and needs regenerated evidence. This is explicit supporting work on the false dispatch branch only.


op36: retained-owned Vec adapter still rejects escaping reference outputs (aeneas-source-op36-retain-opt-resume-array-retain-01). No generic-array/reference preflight was disabled. Native full array gate is next. No row credit.

Fallback scalar two-round shape is proved at 43015: on arbitrary scalar words, the extracted helper returns exactly the packed two successive scalar steps, retaining the full Result. This is not accelerated SHA compression or an op208 source law. It uses symbolic U32 operations and four-element shape/index lemmas, without evaluating a 64-round concrete recurrence.


Native op36 exact gate resume-array-exact-r01 timed out after 180 seconds with no verdict. The named scope was absent from the post-timeout scope inventory; no larger-cap retry. The GNU time wrapper RSS is not claimed as aggregate descendant solver peak. The new short rejection-only gate is prepared separately.


Split native array rejection gate resume-array-reject-r01 passes: input lengths 0–2, arbitrary raw four-limb QM31 values, exact Err output length and arbitrary element index. The 1024-element success branch remains without a verdict. It is not an op36 source law.


Kani resume budget exhausted: 8/8. Six passes (bounded pure String/path/index/error laws) and two 180-second timeouts (full array success/rejection gate; singleton mixed Word pop gate). Neither timeout is a ROW counterexample. Both scopes were checked absent after termination. No SHA compression Kani gate ran. Source rows remain 4 → 5; canonical deployment premises removed remain zero.


Axiom gate: exit-zero diagnostic attempts 43034/43035 used bv_decide and print native certificate axioms. Both are REJECTED despite exit zero; no theorem from them is release evidence. They are being replaced by ordinary kernel proofs. Failed compilation 43036 (unknown add_left_comm lemma) is likewise rejected. Only standard-axiom accepted dependencies may enter the final manifest.


Full owned fallback block extraction is accepted at 43044, exact source identity modulo the recorded namespace/literal ports, standard axioms only, peak 2,675,744 KiB, swap 0. Supporting helper links accepted at 43048. These validate the extracted fallback body, not its complete SHA specification and not SHA-NI. The fixed constant quartets are being validated before the block bridge; no concrete round recurrence is reduced.


Op217 concrete-default monomorphization was attempted with precise/desugared drops (charon-source-op217-mono-resume-concrete-default-01). Charon exited zero but has_errors=true; Aeneas correctly refused the invalid artifact (no Aeneas scope). V237 remains open. No source or tool preflight was bypassed.

Block factoring attempt 43072 reached the default recursion-depth limit while simplifying monadic associativity. It is rejected and is replaced by a small four-round continuation lemma plus explicit staged rewrites, without a depth or heartbeat increase.


Accepted replacement 43081 proves totality of the exact extracted owned fallback block on arbitrary typed 8-word state / 16-word block inputs. The generated proof follows all 147 source binds explicitly, invoking named totality/bounds lemmas; 43080's broad-search heartbeat timeout is rejected. No cap/depth/heartbeat setting was increased. This is a termination/success theorem, not the complete SHA output specification. Canonical scalar recurrence port accepted at 43082. Factored-block bridge drafts (43072/43076/43077/43079) are rejected and archived; their monadic-depth/transparency failures are not counterexamples.
