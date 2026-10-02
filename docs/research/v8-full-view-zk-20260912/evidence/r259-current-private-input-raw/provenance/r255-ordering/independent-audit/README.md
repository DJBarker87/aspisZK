# Independent R255 ordering audit

`audit_independently.py` checks the exact R245 input and R255 output hashes. It decodes hash-consed values, starts from Fun0–Fun16 inclusive, follows typed ADT/regular-function/global references, checks the special Fun `ItemSource::TraitDecl` edge, and validates the resulting order against every dependency. It also compares the independently enumerated edge and integer-ID inventories to the generator audit and compares the complete source JSON after removing only `translated.ordered_decls`.

The audit finds 40 reachable declarations (7 Type, 30 Fun, 3 Global) and 85 typed dependency edges. Every prescribed root is a local body; there are no missing referenced declarations, cycles, AST trait references, special Fun trait-source references, or dependency-order violations. All input rows and other JSON fields remain identical; every reachable declaration appears once.

This is a structural metadata audit only. It does not translate the artifact or establish source semantics.
