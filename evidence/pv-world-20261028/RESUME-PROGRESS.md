# D364 proof boundary during resume

W-CARRIER-1 is a design finding, not a ledger/endpoint counterexample and not
a stop. The initial REPORT's historical stop sentence is superseded by this
resume and the final report will account for the complete resumed budget.

The enriched P state retains statics, atomics, live heap allocations and
ownership, allocator state, per-thread local cells, volatile-write/fence/order
history, unwind state, and runtime-specific Extra. This is interpreter DATA,
not a proved complete native process representation. `dropWitness` now has
an explicit internal event, retains the external flag, increments the witness
counter exactly once, and represents both outcomes. `drop_valid` proves its
full-world threading; `project_threaded` permits deleting an internal event
only when its OS projection is unchanged. No shipped-destructor purity is
assumed or borrowed from unfinished fxmem2 work.

`PV_W_Reservation` reifies the exact frozen `sync_directory`, `reserve_fallible`
and store `reserve` source bodies, including all early returns. Its three
complete-Result erasure laws compile. The generator checks all 34 source call
sites and preserves their order, argument expressions, continuations and
branches. This is a Lean-source correspondence, not a native structural
(K-1 substitute) gate. No Rust rewrite or native finite differential is
claimed here.

`PV_W_ReservationThreading` composes that reification with the independently
defined operational execution judgment. It proves exact returned outcome,
ordered pre-world call list, post-world and trace continuity for interpreted
reservations, given local interpreter-step validity. It also proves projection
through silent process steps. This is more than `valid_bind` alone, but it is
still NOT a proof of the entire extracted prover or an installed deployment
interpreter. Helper functions such as reservation_path still need recursive
interpretations; native primitive adequacy, implicit Drop, filesystem effects
and the complete D159 observer binding remain obligations.

The further typed primitive pass retains File.open/sync_all, OpenOptions.open,
Error.kind and write_all arguments as typed constructors. It avoids requiring
a world interpreter to introspect a thunk or decode arguments from its result.
Remaining helper thunks are explicit subprogram obligations, never classified
as genuinely pure by the mathematical source erasure laws.

The existing OsWorld import cone is being resolved with EJR/freeze/h5
precedence, using only read-only h6 caches with complete transitive object
fingerprints, or private compilation. In particular, differently hashed
tracked files do not override EJR. No source is copied into shared directories.
The original full trust Observation import has a substantially larger cone;
its existence or arbitrary native/extracted equality is not used to justify
an unproved step law.

W-OS-1 and W-OS-2 remain owner findings, never theorem assumptions or new T
fields. Exclusive creation and file-data versus directory-entry durability
remain distinct; crash non-reuse depends on the latter recovery obligations.
All assigned rows remain OPEN. Endpoint premises removed/added/weakened:
0/0/0. Target not yet established.
