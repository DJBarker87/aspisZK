# Excluded attempts and replacements

L001: inspection used nonexistent String.isInfixOf and guessed absent WideExact constants. No theorem/credit. L002 removed the invalid command and discovers actual names, passing.

K005: frozen CM31::write_le_bytes full mutable-slice proof_for_contract hit the fixed 90s CBMC timeout (wall97.063s, RSS6354500KiB, swap0). Excluded. It is never rerun, including under inversion. Replacement: direct same-body fixed-window harnesses with arbitrary selected output byte and no contract instrumentation. KMX matched controls K001..004 remain separate prerequisites. No timeout/cap increase.

E001's generated Funs failed in L009: default signed Rust shift literals are emitted as I32 arguments to a U32-only library wrapping_shr. No generated proof was patched. E002 changes the safe reference's shift literals to explicit u32, retaining the identical bit-shift values and semantics. E001/L009 excluded.

L015's bv_decide proof printed two generated native bv_decide axioms. It is excluded despite exit0. Replacement uses BitVec bit extensionality and symbolic index bounds; no reflection/native axiom is accepted. L011..L014's failed reference-equality drafts are excluded, including automatic sorryAx diagnostics.

K056 failed compilation before CBMC: the exact KMX generic Vec helpers require allocator_api in the program-root harness crate. Corrected the private scratch root with cfg(kani)-only feature(allocator_api), matching the existing core-root harness configuration. Lock postcheck unchanged. Replacement keeps the original copy4096_positive harness name (K058); no verdict was renamed.

K068's matched short-control inversion fails exactly its two intended mutually exclusive branch assertions (zero length and nonempty length); every other check passes. The private controller incorrectly expected one failure universally and stopped after collecting the valid receipt. The controller now accepts precisely those two assertion texts for K068 only, preserving the one-failure gate elsewhere; K068 is not rerun.

K069's generic n=5..80 arithmetic-free dot control trace hit the fixed 90s CBMC timeout; excluded and not rerun. The split uses the actual state_only_poseidon.rs:525..533 seven-term caller, n=7, with the original long_control harness name and assertions. It supplies seven-term control only; other long lengths remain an explicit domain finding. K070/K073 are the new constant-seven pair, not a negative replay of K069.
