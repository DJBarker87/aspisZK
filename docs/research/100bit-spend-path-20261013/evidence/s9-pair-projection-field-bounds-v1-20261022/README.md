# S9 projection-body field-index bound

The successful generated `pair_s2_libra_parts_projection_loop.body` theorem
shows that its same execution successfully reads `libra[j]` from an array of
length four. That read yields `j.val < 4`. The same body execution also
successfully calls the pair caller's `weights.field f j`; the owned-reader
bridge supplies the corresponding owned call and canonicality, and the
bounded-index bridge rewrites that exact owned call to the generic checked
reader at the same `j`.

This closes the field-index bound for this accepted generated body, without a
caller index premise. The theorem is limited to this body call and its linked
owned-reader operation bridge. It does not establish a whole Rust caller or
runtime/binary refinement.

The main theorem compiled with Lean 4.32, exit status 0, in 23.345 seconds at
3,191,996,416 bytes peak aggregate RSS with zero swaps. Its axiom report is
`[propext, Classical.choice, Quot.sound]`. The first attempt is retained under
`failed-attempts/v1`; it failed during import resolution and is not proof
evidence.

Run `python3 -B check_packet.py` to validate source/receipt pins, imports,
axiom report, closure, linked packets, and the selected V8 owner map.
