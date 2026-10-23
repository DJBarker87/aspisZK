# S9 compute allowance and source-proof choice

Status: measured candidates; neither adopted. Owner decision pending. The
current allowance remains +12,000 CU relative to the approved S4 artifact.
The 100-bit security target is unchanged and is not yet established.

Both options below use C weights
`ab55509e54218a2bfe7dd2d5e1b14216e3303961c16c181ce2e03d40f6b7678b`
and the current owned adapter with the callback-free tail-slice zero scanner,
adapter hash
`246d96b479ef552b485a51a2a3d4c4dbe1ff4ef9c0527b6f9a872f296b60576b`.
The scanner preserves byte order and checks every checkpoint byte; its
all-input source-equivalence proof remains required. No check is removed.

| Candidate | Maximum six-fixture stage-1 increase | Maximum six-fixture settlement increase | Additional source-refinement issue |
| --- | ---: | ---: | --- |
| H5: retain C fast-pairing bodies | 12,214 CU | 2,294 CU | Tail scanner equivalence and source/artifact integration |
| H11: restore only `canonical::Dot::finish` four-element `.map(reduce)` | 11,342 CU | 2,294 CU | Same scanner work, plus original Rust Std `Array.map` correspondence |

All six accepted runs have matching checkpoint tails/return data and passing
strict-stack gates. The approved comparator is ELF
`dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`.

H5 retains fast-pairing source
`7f75b58bfcaf7f586acb0152671e42565a549a8ace2b90dab794533dcdb6335e`;
its artifact is
`b5cb382b1738a016b2463d2388fd38523e55577bf8053b7b4f68aee482fa4d5b`.
H11 changes only Dot::finish relative to H5; fast-pairing source is
`0e3f01ca12dfb243319363f8748e63b442853ca3130d6bd940ec6347f3eac64b`,
artifact
`ca4dfbd90be40fbb97d72494fa2a8f399fac732482c10f92e9c82f6ee18a49bf`.

## Retained full-random-mask proof check

Both were checked against the same retained OS-random-mask proof and the
same approved comparator. These are one-sample measurements, not a new
random draw, a distribution test, a cost-independence theorem or an
analytical worst-case bound.

| Candidate | Stage 1 CU | Comparator stage 1 | Increase | Settlement CU | Comparator settlement | Increase |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| H5 | 1,208,282 | 1,196,068 | 12,214 | 1,142,223 | 1,139,924 | 2,299 |
| H11 | 1,207,410 | 1,196,068 | 11,342 | 1,142,223 | 1,139,924 | 2,299 |

Checkpoint and return bytes match; neither run reports an error. H5's
immutable retained evidence is
`/home/dombarker/project-offloads/pair-s9-cu-attribution-h5-tail-zero-v1-20261023/full-mask-candidate/result/evidence.json`.
The attribution worker is packaging exact source deltas, build/recompile
logs, cgroup receipts and fixture data without binaries or task keys.

## Recommendation

Allow a measured increase of +12,214 CU, 214 beyond the current allowance,
and retain H5's callback-free fast-pairing bodies. This avoids reopening
Std `Array.map` source refinement after the explicit C bodies were proved.
The C arithmetic bodies and their existing proof work stay applicable.

H11 is a real alternative within the existing allowance. Its original
Dot::finish source matches an older checked emitted cut, and the four
coordinate reduction equations are already proved. That historical packet
explicitly leaves actual Rust Std `Array.map` correspondence open. It must
not be silently treated as an established source theorem.

Annotation-only attempts on snapshot, require_zero and Dot::finish did not
recover the final 214 CU. Explicit four-word destructuring produced exactly
the H5 artifact. An OR8 scan saved only 220 CU from the earlier indexed
scanner; a `u64::from_le_bytes` scan was worse. Reverting all fast-pairing
bodies meets the allowance but adds more proof re-pins than H11 and is not
preferred. A stale-cache H3 run was rejected; accepted builds explicitly
recompiled both cost-probe and program crates.

Either choice still requires scanner equivalence, relevant source re-pins,
release integration gates and final artifact linkage. A change to the CU
allowance establishes no additional soundness, privacy or runtime theorem.
No allowance change is inferred without an actual owner response.
