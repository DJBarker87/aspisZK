# R510 expanded-hashcons projection translation receipt

This is a failed translation receipt, not a proof result.

Preflight expanded every `Deduplicated` reference from the complete original
R500 table with fail-closed checks: 182 definitions, 2,120 references, no
missing IDs, no cycles, and no wrappers in the expansion. It then retained
only fully expanded function rows 1, 32, and 33; added ordered Fun1 before
Fun32; and audited retained-row equality against the expanded original.

The single authorized R510 translation used the pinned R497 binary in its
fresh capped remote workspace. It exited 1 after 0.10 s, peak RSS 51,568 KiB,
and zero swap. No Lean output was generated or compiled.

The decoder stopped while parsing expanded (unwrapped) type content. Its first
reported failure is `Charon__Generated_OfJson.hash_consed_val_of_json` on a
raw `Adt` type value, reached through `name_of_json`. The existing input
codec therefore expects hash-cons wrapper form at those positions; a fully
expanded JSON representation is not accepted by this binary. This is a
serialization result only. It makes no source-semantics or proof claim.
