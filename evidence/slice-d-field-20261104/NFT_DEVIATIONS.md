# Excluded attempts and replacements

L001: inspection used nonexistent String.isInfixOf and guessed absent WideExact constants. No theorem/credit. L002 removed the invalid command and discovers actual names, passing.

K005: frozen CM31::write_le_bytes full mutable-slice proof_for_contract hit the fixed 90s CBMC timeout (wall97.063s, RSS6354500KiB, swap0). Excluded. It is never rerun, including under inversion. Replacement: direct same-body fixed-window harnesses with arbitrary selected output byte and no contract instrumentation. KMX matched controls K001..004 remain separate prerequisites. No timeout/cap increase.

E001's generated Funs failed in L009: default signed Rust shift literals are emitted as I32 arguments to a U32-only library wrapping_shr. No generated proof was patched. E002 changes the safe reference's shift literals to explicit u32, retaining the identical bit-shift values and semantics. E001/L009 excluded.

L015's bv_decide proof printed two generated native bv_decide axioms. It is excluded despite exit0. Replacement uses BitVec bit extensionality and symbolic index bounds; no reflection/native axiom is accepted. L011..L014's failed reference-equality drafts are excluded, including automatic sorryAx diagnostics.
