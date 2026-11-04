# Excluded attempts and replacements

L001: inspection used nonexistent String.isInfixOf and guessed absent WideExact constants. No theorem/credit. L002 removed the invalid command and discovers actual names, passing.

K005: frozen CM31::write_le_bytes full mutable-slice proof_for_contract hit the fixed 90s CBMC timeout (wall97.063s, RSS6354500KiB, swap0). Excluded. It is never rerun, including under inversion. Replacement: direct same-body fixed-window harnesses with arbitrary selected output byte and no contract instrumentation. KMX matched controls K001..004 remain separate prerequisites. No timeout/cap increase.

E001's generated Funs failed in L009: default signed Rust shift literals are emitted as I32 arguments to a U32-only library wrapping_shr. No generated proof was patched. E002 changes the safe reference's shift literals to explicit u32, retaining the identical bit-shift values and semantics. E001/L009 excluded.

L015's bv_decide proof printed two generated native bv_decide axioms. It is excluded despite exit0. Replacement uses BitVec bit extensionality and symbolic index bounds; no reflection/native axiom is accepted. L011..L014's failed reference-equality drafts are excluded, including automatic sorryAx diagnostics.

K056 failed compilation before CBMC: the exact KMX generic Vec helpers require allocator_api in the program-root harness crate. Corrected the private scratch root with cfg(kani)-only feature(allocator_api), matching the existing core-root harness configuration. Lock postcheck unchanged. Replacement keeps the original copy4096_positive harness name (K058); no verdict was renamed.

K068's matched short-control inversion fails exactly its two intended mutually exclusive branch assertions (zero length and nonempty length); every other check passes. The private controller incorrectly expected one failure universally and stopped after collecting the valid receipt. The controller now accepts precisely those two assertion texts for K068 only, preserving the one-failure gate elsewhere; K068 is not rerun.

K069's generic n=5..80 arithmetic-free dot control trace hit the fixed 90s CBMC timeout; excluded and not rerun. The split uses the actual state_only_poseidon.rs:525..533 seven-term caller, n=7, with the original long_control harness name and assertions. It supplies seven-term control only; other long lengths remain an explicit domain finding. K070/K073 are the new constant-seven pair, not a negative replay of K069.


L048's dot draft omitted explicit imports. L049 imported the unprefixed legacy FJh module and discovered a missing RawPoseidonExternalRows dependency; L050 similarly found an absent legacy nested-set object. All are rejected. L051/L052 switch to the already pinned coherent RPv_ module graph, retaining canonical namespaces/definitions and existing private objects. No old S1/old-FIo forest or duplicate Phase owner was imported. All selected input object hashes are recorded.

L053's fourth-product draft failed to unfold overloaded scalar arithmetic (sorryAx diagnostic excluded). L055 changes the proof to explicit UScalar.mul/add and derives exact value from successful primitives; standard axioms only. L057 extends the product-budget proof and records that the selected Probe/FIq environments have no definition of the generic accumulation/small helpers. Those helpers remain OPEN despite native support.

Other failed drafts L006/L022/L026..028/L033/L036..037/L041..042/L044 are fully preserved and excluded. They correct local identifier, array/size or elementary finite-list elaboration errors; only later current source hashes with successful receipts and raw audit enter certificates. All60 Lean/support labels are charged, including failures. E001..003 each consumed an extraction slot, even though E001's reference was rejected.

Final L060 optimized link, eight fixtures and58 new raw roots passed in49.355s, RSS5708408KiB, swap0. Source-only strictness additions to the NFT validator check copy-pair identical sources/environment, raw graph hashes and current source-to-successful-compile matching; baseline NFQ/NFK validators remain unchanged. No proof/release replay followed this evidence validation.
