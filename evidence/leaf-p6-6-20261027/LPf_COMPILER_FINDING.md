# Fixed-slice stubbing finding

LPf_K015 verifies the native CM31::write_le_bytes contract on exactly8 output
bytes for arbitrary raw32-bit inputs. LPf_K016's QM31 parent uses stub_verified
on that same actual callee but Kani0.67.0 panics during code generation:
`reachability.rs:419:69`, unwrap Err: failed to resolve
`core::iter::IntoIterator::into_iter` for mutable nested slice `[[u8]]`.
No parent proof or semantic failure is inferred. Full pinned stderr is retained.
No launcher/compiler/monitoring infrastructure was edited. The next proof-contract
isolation replaces dynamically sized slice footprints by the explicit8/16 byte
locations, with exactly the same precondition len8/len16 and postcondition.
A fresh callee contract proof is required before substitution. If it fails, the
parent/checkpoint gates remain OPEN; there is no arbitrary successful stub.
