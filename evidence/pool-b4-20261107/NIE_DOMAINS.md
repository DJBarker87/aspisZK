# NIE domains

Native marker recheck cuts use valid AccountInfo handles with arbitrary keys, lamports/rent and 0..3-byte logical slices, System owner distinct from Pool, specified privilege branches, and an optional existing shared alias. No exclusive guard is initially live in this LOCAL harness domain. This domain is NOT adopted as the production domain: caller establishment is exactly OPEN.

Model SharedRoom means 0 <= counter < maxCounter for the same interpreted account data cell. Cell identity is supplied explicitly; key inequality never substitutes for allocation disjointness. Shared round-trip results cover arbitrary cell aliases and ambient/payload state. They assert nothing about CPI, realloc, guard leaks/splits, lamport borrows or runtime-entry initial conditions.

The production domain must be derived from actual root/runtime admission and every intervening callee and implicit cleanup, including arbitrary account aliasing. NHP_K086 remains outside no PROVED production domain yet. Existing acceptance/trust/source-to-ELF hypotheses are unchanged.

The decoder/recheck observations quantify the selected logical byte window, balance, borrow cleanup and the explicit key/owner/flag checks in each source. They do not by themselves cover the entire physical backing outside that view, every Rc field or rent_epoch. The complete production frame remains OPEN. The empty modifies list in an observation shape is an intended candidate footprint, never a substitute for a certified frame contract.

Domain finding D-1: none of the bounded decoder, recheck, post-entry-guard or all-Some token cases can be substituted as a complete production callee PacketDomain. Production callers do not establish those stronger local restrictions. These observations remain partial and uncredited as composed rows. In particular accepted custody requires the no-option configuration; the all-Some parser projection is a separate rejection-input case, not a proposed custody admission.
