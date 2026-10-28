# Function inspection, unchanged source

The inherited BuilderForestAdmissionPort is not re-extracted here. Reuse runjoin17's parent/hash fidelity inspection and D287 native fixture results, with the limits stated there. No new native differential or ELF replay is claimed.

* OwnedTree.from_parts: owned record construction and validation; no borrowed-element write.
* validate_owned / validate_owned_loop: read-only frontier/empty reads; result threaded. No discarded restoration continuation.
* OwnedTree.append_one_loop: index loop with explicit Array.update and recursive passing of the changed frontier. Rust reference tree.rs 27–31 uses frontier[carry_level] = empty[carry_level]. The changed array is retained in the emission. At these fixture indices the carry loop makes no write; the subsequent nonfull append writes frontier[0] = leaf.
* OwnedTree.append_one: Array.update frontier carry_level root is bound as frontier1 and placed in both provisional reconstruction and final inner record. No discarded back/restoration result. Checked equations will compare this changed frontier to the explicit retained native fixture, rather than inferring it from the root alone.
* reconstruct_nonfull_root_from_level[_loop]: shared frontier/empty reads and owned node updates only. Every parent result is threaded recursively. No indirect mutable borrow.
* late_append, from_parts_with_empty_roots, append_one_with_empty_roots: owned result/map forwarding. The `_` in `(next, _)` drops the receipt, not a restoration continuation.
* bank row/block/rows: read-only Vec columns; block absorption writes via explicit Array.update, then passes the changed state recursively. No dropped restoration continuation in these wrappers. `evaluate_trace_round_pair` uses owned state, preserving each returned state. Underlying arithmetic calls retain their separate proof/fidelity obligations.

SDY overlap remains covered by ruling (o), not by a repeated scan here. These checks do not assert general extraction fidelity or source/deployed identification.
