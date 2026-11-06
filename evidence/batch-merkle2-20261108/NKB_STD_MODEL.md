# NKB padding standard-library model

Target not yet established. No parent row is claimed CLOSED.

## Scope and justification under (au)(3)

The opaque Iterator::any is interpreted by Port3_BatchStd.anyDefault and NKB_AnyModel. The constructor/next equations in Port4B_AnyFalse.body_nil/body_cons are rfl on the pinned Aeneas ChunksExact representation; selected Aeneas object hashes are in each Lean receipt. NKB_AnyModel.total proves the complete finite scan, both Boolean outcomes, short-circuit remainder of chunks, and unchanged partial-byte remainder. Its callback is concrete and returns normally on every eight-byte chunk, proved by NKB_PaddingPredicate.source. NKB_AnyModel.false_iff identifies false with every chunk byte zero. NKB_PaddingFrame.aligned removes an ignored partial suffix for the actual fixed slot. No caller success, arbitrary Ops dictionary or free runtime Bool is introduced.

The documented Rust semantics are [Iterator::any](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.any) and [ChunksExact](https://doc.rust-lang.org/std/slice/struct.ChunksExact.html). any stops at the first true predicate, returns false on exhaustion/empty input, and leaves later elements unconsumed. ChunksExact visits consecutive disjoint full-size chunks and retains a smaller trailing remainder. These API specifications were read from the official 1.99.1 documentation; no identity of that documentation's implementation with the pinned compiler's std body is claimed. The actual native differentials use the job's pinned Kani configuration.

K015/K016: exact frozen eight-byte predicate, arbitrary eight bytes, value iff nonzero array. K017/K018: ONE actual ChunksExact::next, arbitrary remaining length <=5504, head bytes/length/address, remaining full-chunk count and unchanged remainder. K021/K022: actual std Iterator::any with the exact frozen predicate, zero or ONE complete chunk and arbitrary 0..7-byte remainder, exact result, callback count and iterator/remainder frame. These are the kit-method-3 fidelity checks, not a native whole-buffer proof. Generalization over all chunks is the Lean induction plus the existing documented-stdlib/P7 interpretation under (au), not unwinding a large scan. K009 is retired; no timeout or cap was increased.

No multiplication, SHA implementation, function contract, Option<fn>, writable static, new copy stub or new trust row is used. KMX patch is unchanged. Native semantic transport and this std interpretation retain the existing P6/D188/P7 boundary as RECLASSIFICATION, never premise removal.
