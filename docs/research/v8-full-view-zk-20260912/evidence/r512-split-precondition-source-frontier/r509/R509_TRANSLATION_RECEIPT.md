# R509 null-slot projection translation receipt

This is a failed translation receipt, not a proof result.

The input was mechanically projected from the exact saved R500 LLBC by retaining
only complete function-table rows 1, 32, and 33; retaining all non-function
tables unchanged; and adding ordered Fun1 immediately before ordered Fun32.
The projection audit records structural equality outside `fun_decls` and
`ordered_decls`, retained row equality, and the original target's sole
function dependency Fun32 -> Fun33.

The one authorized translation ran on the pinned R497 binary in a fresh capped
remote workspace. It exited 1 after 0.09 s, peak RSS 50,336 KiB, zero swap.
No Lean files were generated or compiled.

The decoder stopped before prepasses at retained Fun1's signature reference
`{"Deduplicated":3327}` with `Hash-consing key not found`. The projection
removed function-table slots that contained hash-consed value definitions still
referenced by retained rows. This receipt records only that serialization
closure failure. It makes no claim about source execution, the native helper,
or any proof obligation.
