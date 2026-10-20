# Count-derived EbyK decoded product update

This theorem composes the accepted per-call decoded product update with the count-indexed accumulator invariant. Given `sumsBelowCount self.count.val` for both Dot states, success of the actual QRaw-backed push yields the product-update equations without independent `< 2^46` accumulator premises. Those strict pre-call bounds are discharged from the source push guard `count < 4096`.

The poststate is count-indexed and may reach count 4096 with lane values bounded by `≤ 2^46`; the theorem does not claim strict inequality for that terminal state. Exact outer caller traversal and fresh accumulator initialization remain open.

This packet contains the exact source and focused run records; it omits compiled objects. Its direct dependency is the adjacent `eby-k-dot-count-bound-v1` packet.
