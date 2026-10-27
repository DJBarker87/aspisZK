# Op4 P6 reference and source association

Target: replace only op4, after Op3I_Accepted, with the whole extracted owned
reference; derive frozen2 scan on the SAME accepted f.proof. No scan-law premise
is permitted. S2 remains OPEN until Kani equivalence and Lean composition pass.

Reference source is kit/src/Op4P_reference.rs. Its recursive canonical_word,
canonical_qm, check_values, read16, canonical_words, opening_scan, opening_rows,
and scan bodies reuse the existing checked MultiproofParserRef extraction.
canonical_scan adds the ordinary Result<(), Parse> carrier; all input is shared
immutable bytes, with no oracle, allocator or mutable effect.

The Kani source kit holds byte-identical shipped canonical_scan, opening, echeck,
and compact::check_values bodies (only canonical_scan visibility is widened).
It uses the actual aspis-core field decoders. Error is nominally reduced to Parse,
the only reachable variant; codec conversion always maps to Parse. The explicit
layout constants are subject to an independent source-pin check. This is an
experimental evidence kit, not a changed shipped implementation. Source-to-ELF
and P6 trust retain their existing scope.

Budgets: 0/80 Lean, 0/40 Kani at stage creation. No validation result yet.
No files under crates/ or programs/ changed; ELF rebuild trigger has not fired.
No wallet keys touched. No push.
