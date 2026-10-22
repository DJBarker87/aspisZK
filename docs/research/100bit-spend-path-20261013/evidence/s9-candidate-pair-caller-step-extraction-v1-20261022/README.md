# S9 candidate pair caller-step extraction

This packet records a candidate-only Charon/Aeneas extraction of the `S2`
`factored_s2_libra_weights` call and the following four-iteration `parts[4]`
update slice in `Weights::pair`. It does not prove the full pair caller,
production equivalence, or S9 end-to-end reachability.

The candidate helper source is pinned by SHA-256
`9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf`; the
frozen `weights.rs` is pinned by
`28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137`. Their
`Weights::pair` function bodies are byte-identical (body SHA-256
`1a56a621c8fe09855427e242a59f876b61d48d1d5f1c06ec99db342d6ac75510`). The
isolated extraction harness adds only the projected method and a root shim;
the source checker verifies this exact delta.

The reached field reader is also pinned: candidate and frozen
`pub fn field(bytes, i)` bodies are byte-identical (90 bytes; body SHA-256
`0be69c81ca5a33634bb1f9440b904d6d83ecb7b3336061eee9932473cd100445`) and
perform `E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap()`. A retained S3
field-readback theorem already reconstructs the checked slice and successful
source parser result for this function shape. This extraction nevertheless
leaves the newly generated `weights.field` operation as an axiom: its use of
that existing theorem still requires an explicit carrier-map/source binding.

Attempt 1's Charon process itself exited 0 and emitted the retained LLBC
(SHA-256 `07dcd90dffb290fde3560a3841595aa11f38870a89a1a815990567ae9234b2eb`).
The outer wrapper then exited 1 while serializing metadata for a declaration
with null `item_meta`; no Charon rerun was made. Attempt 2 reuses that exact
LLBC and Aeneas exited 0 under a verified direct cgroup scope with
`memory.high=2 GiB`, `memory.max=4 GiB`, and `memory.swap.max=0`.

Generated Lean includes a transparent `pair_step_root`, transparent
`pair_s2_libra_parts_projection`, transparent projection loop, and the
transparent factored helper. The fallback `twofold_libra_weights` and
`weights.field` remain opaque. The generated external template contains eight
axiom declarations for arithmetic operations, `weights.field`, and the
twofold fallback. These are diagnostic Aeneas boundaries only; they were not
accepted as proof assumptions or compiled. No Lean compile or `#print axioms`
audit was run for this generated output.

The extraction still needs an actual typed binding for `weights.field` to the
source-byte parser and the exact selected field-operation adapter before the
four-slot update can be consumed semantically. It also retains the non-S2
fallback as an opaque boundary. No production source was modified, and no
compiled binaries or Lean object files are included.

Run `python3 check_packet.py` from this directory to verify the source pins,
LLBC/output hashes, generated declaration shape, and source-only packet
contents.
