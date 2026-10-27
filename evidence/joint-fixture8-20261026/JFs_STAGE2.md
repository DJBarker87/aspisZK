# Late public decoder

`JFs_LateDecode.source` proves native boxed late-statement decoder success on
public1880[144:1664], with exact inherited snapshot and afterstate values.
Header lengths32/800/688/1520, both boxed child calls and next-index13→14 are
proved without child-success premises. Atomic source reads are composed using
small windows; no whole-public normalization is used.

Attempts007–015: seven passes and two rejected drafts (009 rangeFrom list shape;
013 invalid refolding syntax). Final exact hashes have accepted receipts.
15/100 Lean;0/10 Kani. No timeout/memory kill. Standard axioms only.
No top premise removed. Complete public decoding/serialization is next.
