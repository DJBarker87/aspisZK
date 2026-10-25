# SOURCE1161: concrete component results and remaining potential proof

`Port11PROV_SourceCount` applies the existing physical Code budget interpreter
to the actual emitted owned helpers, including native fail/div policy and
post-hash checked writes:

- `leaf_bound/leaf_count`: at most one actual oracle read for any physical
  `Port4B_LeafCode.code` input, including malformed openings and any kind.
- `parent_bound/node_bound/node_count`: at most one read through each actual
  supplied/occupied sibling branch. Short physical buffers and every checked
  pre-read failure are included; a read whose following mutation fails is
  counted. There is no accepted-return restriction.
- `rows_bound/rows_count`: the actual `Port9OR_P6Rows.rows fuel` physical
  traversal has at most `fuel` reads on ALL outcomes and arbitrary initial
  scratch/index/write positions. This uses induction on the emitted loop,
  not a model count theorem or normalization of18 concrete levels.
- `writer_bound/writer_count`: installed physical op8 emits at most3 reads
  on all states/inputs and partial digest policies. `Port9OR_Budget.reader_count`
  is explicitly REUSED for physical current18's all-input cap3.

These are concrete component counts, NOT a native op5/driver1161 certificate.
The generic `mono/bind_bound` are used only as supporting structural lemmas;
the delivered count statements above mention the actual physical code.

## Inspected source paths

`Port9OR_BatchStep.body` hashes before the previous-index/digest comparison.
A duplicate accepted or rejected leaf therefore consumes its leaf read; it is
not removed from the physical observation. Count failure, capacity failure,
nonzero padding, node slice/scan failure and other early exits precede physical
verification. If physical verification is reached, it receives the actual
used node prefix, not the full padded slot. Each of the3 trees short-circuits
before the next tree on failure. The driver calls batch0 then writer/current18
then batch1, and retains all earlier observations even on rejection. Later
source/annotation sampler reads are a separate experiment component.

The capacities in installed op5 are146,146,128,172,172,150 (sum914); the two
actual leaf-loop sizes are10 and12 for each of3 kinds (66 physical leaf calls,
including duplicates). The expected native count argument would bound parent
reads by supplied siblings plus occupied merges:914+(66-6)=974; leaf+parent
1040, checkpoint writer/reader6 =>1046; transcript115 =>1161. This is a
SOURCE-AUDIT CALCULATION TO PROVE, not a formal native bound. It is NOT inherited
from the model's1161 theorem, nor asserted as a corrected security bound.
No physical counterexample to1161 was established in this job.

The exact missing owned theorem is a read/potential invariant for the reached
physical rows/levels, preserving the source cursor and unresolved frontier:
`frontier = n-i+w` inside a row traversal, followed by n=w at the level cut.
A successful occupied merge decreases that frontier by1; a supplied sibling
consumes32 bytes while preserving frontier. Compose across heights and the
actual used-prefix count guard, including the last executed read before any
error/Stop; do not insert rejected suffixes or deduplicate calls. The current
per-fuel cap alone cannot prove1040, because it does not relate partial row
outputs to source cursor/frontier changes. This is explicitly not packaged
as a generic count premise pretending to prove source1161.

The driver additionally delegates op3/4/7/6/17/etc. to `rest`. Their physical
oracle budgets (especially the effectful preparation's115 transcript reads)
are not bounded by batch/checkpoint certificates. Unrestricted `rest` can
issue arbitrarily many reads. Thus an unconditional driver1161 theorem over
the CURRENT interpretation's arbitrary `rest` would be false. An actual owned
rest implementation and its source-call budgets are required; this is the
same Session A producer boundary found during provenance composition.

## Preserved failures

001: wrong scalar rewrite/injectivity theorem names; replaced with explicit
source values and existing `digest_of_bytes`.006: literal Usize/Nat index
rewrite mismatch; explicitly changed the source indices.007/009/010:
structural budget monotonicity, ambiguous bind/read names and base-case proof
shape; replaced by symbolic monotonicity/composition and explicit base case.
014: reserved parser token as a local identifier; renamed.016: scalar length
normalization and reserved `prefix` name; corrected.019/020: source query-byte
option equality/address normalization; corrected before retrying. Every
source/log is retained. No resource failure, raised cap, unchanged failed
retry or unoptimized arithmetic job occurred.
