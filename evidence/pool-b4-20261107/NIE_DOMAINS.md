# NIE domains

Native marker recheck cuts use valid AccountInfo handles with arbitrary keys, lamports/rent and 0..3-byte logical slices, System owner distinct from Pool, specified privilege branches, and an optional existing shared alias. No exclusive guard is initially live in this LOCAL harness domain. This domain is NOT adopted as the production domain: caller establishment is exactly OPEN.

Model SharedRoom means 0 <= counter < maxCounter for the same interpreted account data cell. Cell identity is supplied explicitly; key inequality never substitutes for allocation disjointness. Shared round-trip results cover arbitrary cell aliases and ambient/payload state. They assert nothing about CPI, realloc, guard leaks/splits, lamport borrows or runtime-entry initial conditions.

The production domain must be derived from actual root/runtime admission and every intervening callee and implicit cleanup, including arbitrary account aliasing. NHP_K086 remains outside no PROVED production domain yet. Existing acceptance/trust/source-to-ELF hypotheses are unchanged.
