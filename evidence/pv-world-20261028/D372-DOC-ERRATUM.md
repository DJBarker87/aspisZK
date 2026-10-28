# Transformer terminology in the inherited calculus comment

The opening comment of the pinned `PV_W_Threading` source reverses the usual
transformer terminology: StateT over an error monad loses the post-state on
failure; an error transformer over a state monad can retain it. The actual
`Run`/`bind` definitions here explicitly retain the post-world and call prefix
on failure and divergence, as checked by `bind_fail` and `bind_div`. No theorem
or native claim relies on that comment. The pinned source is unchanged, and
this erratum corrects the prose without invalidating the audited source hashes.
