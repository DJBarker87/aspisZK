# Add-small compatibility candidate: checked arithmetic and writeback

PROVED for the selected explicit Std compatibility owner: the wrapper restores the result of applying the loop's state transformer; a successful iteration retains the updated digit; the emitted U64 arithmetic pipeline succeeds for digit<P and addend≤257 with exact Nat remainder/quotient values; and the bounded one-step theorem derives those arithmetic results rather than assuming them.

CANDIDATE compatibility boundary: the selected old-v5 outer wrapper was manually repaired from `into_iter_back back` to `into_iter_back (back iter)`. It is not unchanged raw emitted code. The original external ABI expects an iterator state; the raw wrapper's argument is a transformer. The source snapshots and exact diff are recorded under `wrapper-provenance/`. A later source-indexed Rust candidate avoids that interface, but is not part of these four proof results.

The Std-operation interface, whole iterator traversal and eight-digit carry invariant are OPEN. No current Rust-equivalence, gamma distribution, low-base or production-adoption claim is made. The complete retained owner is included for review only; its unrelated low-base adapter was previously rejected and is outside every claimed theorem here.

Four focused NUC targets passed at -M4400 with explicit caps and swap0. All printed theorem axioms are standard. Exact source/import/object/compiler pins, commands, RSS and time receipts are retained without binaries. No unchanged replay was performed for publication.
