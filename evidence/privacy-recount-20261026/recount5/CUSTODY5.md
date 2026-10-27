# N7 — custody record, outside the privacy row denominator

D284 corrects D272. The Rust harness creates its fixture witnesses internally.
The private input at the Python→devnet_spend signing boundary is the 32-byte
Ed25519 seed inside each 64-byte Solana keypair JSON file; decimal-byte parsing
leaks magnitude classes. This is a signing-key custody side channel, not a
privacy-witness finding. No new privacy row or trust field is added.

The pinned n7 branch prepares, without applying to the candidate, the patch
`evidence/pv-n7-20261027/patches/0001-private-key-raw-fd.patch`: 4,951 bytes,
SHA-256 66aa36518ada24bda6dc2727ee9df97d7ccb6913883855afbd922b60a61d7cc8,
+50/−4 lines in Python and standalone Rust client. Python parses existing files
and writes fixed 64-byte records over an inherited pipe; Rust uses a fixed copy.
Eight fixed-offset MOVUPS plus RET are measured decoder instructions, with no
conditional branch/secret-selected address in that body; V371 remains relevant.

Measured scratch evidence: two proof fixtures and statements byte-identical
(action=prove does not execute key loading); separate public RFC8032 signing
fixture produces the same 158-byte signed transaction; short/extra input rejects.
The three retained ELF hashes match, with unchanged crates/programs sources;
these are not fresh SBF rebuilds. No key/fund operation occurs in this recount.

Owner adoption and client recipe/scope remain pending. Python decimal parsing,
secret-file storage, memory lifetime/zeroization, OS pipe scheduling/partial
reads/failures, keypair validation and Ed25519 signing retain their custody and
complete-observer obligations. No whole-client constant-time or privacy result
is inferred. Evidence: n7:design/PV-N7-20261027.md and INVENTORY.md, at pins.json.
