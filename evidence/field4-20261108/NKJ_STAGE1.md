# Stage1 reference extraction

E002 succeeds with NCO tool hashes (Charon then Aeneas), value-passing fixed arrays and explicitly constructed rows; no loop or nested mutable array borrow. Raw emissions retained. Extraction uses optimized release arithmetic (wrapping); the canonical/bounded domain must discharge equality to the adopted checked model, never a global equality claim.

Generated Types/Funs copied byte-identically. FunsExternal is a new explicit definition binding the converter to NGA_SmallResult.convert and transporting the four raw limbs; it introduces no axiom. L001/L002/L003 pass in the coherent NKH paths. Native segment work remains open; K001 is an allocator_api compilation error from the exact KMX include, repaired only by a cfg(kani) crate feature in scratch.

S002 collector failed on binary snapshots after successful setup; collected read-only, never rerun. Binary handling is now lossless base64 and compression. These are owned-script repairs, not host-infrastructure changes.
