# Independent R246 ordering audit

`audit_independently.py` checks the exact R245 input hash and R246 output hash, then independently decodes Charon hash-consed values and follows only typed ADT, regular function, and global references from the prescribed roots Fun 0–5 and 7–16. It checks declaration rows are unchanged, the full JSON differs only in `translated.ordered_decls`, all references resolve, there are no cycles or trait dependencies, and every dependency precedes its user. Its edge and integer-ID inventories are compared with the generator's audit.

R246 reaches and emits 35 declarations: 5 types, 27 functions, and 3 globals, with 70 typed dependency edges. No missing refs, cycles, trait dependencies, or edge/census discrepancies were found. Fun6 (C::input) remains in the original declaration table byte-for-byte but is not a root, not reachable from this closure, and not emitted. The adjacent R246 README explicitly records that it remains unproved due to Option try-trait dictionaries.

This audit validates only metadata ordering and structural closure. It does not translate the projection or establish source semantics.
