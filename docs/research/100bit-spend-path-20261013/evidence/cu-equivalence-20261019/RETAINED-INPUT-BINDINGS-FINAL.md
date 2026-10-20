The complete retained source preparation now supplies the invariants needed
by canonical dot operands and the S2 Libra replacement. The entry theorem is
`CuSavingsRetainedPreparationInputs.preparation_inputs`.

The common preparation record is specialized computationally: scalar invokes
the actual source CanonicalSampler.scalar with coordinate-only Digest,
transcript and wide-field copies; powers invokes the actual source generic
powers builder. All other unchanged common computations remain shared. The
optional `sameBlock` specialization makes wide scalar and scalar_k use the
same source Transcript.block leaf, with exact transcript/Digest copies.
There are no canonicality, success or equivalence proposition fields.

The common verifyObserved record is specialized to the existing complete
VerifyPrefix.verify(FinishModel.finish R B), with full Public, Verified,
Error and Phase carrier copies. Actual whole verify success supplies the
finish witness; actual semantic rounds then supply every one of the ten
semantic alpha values' canonicality. No finish-success premise is supplied
by a caller. The actual Prepared.new return copies that semantic alpha array
unchanged.

The final theorem consumes successful complete tx1_prepare execution, not
separate child successes. It derives both sampled S2 alpha origins, a source
origin for every entry of the returned 29-element gamma scratch table, and
canonicality of every returned semantic_alpha entry (including the two extra
coefficients at indices 8 and 9). The actual folds=2 result selects the S2
branch; the general preparation result separately records the singlefold
second alpha as zero. Parsing, semantic/preparation errors and divergence are
not silently treated as successful source executions.

Ten focused targets are green, using only standard Lean axioms. Selected
sources and direct import object hashes are coherent. The final entry target
ran in 2.005 seconds, peak RSS 3,807,632 KiB, with zero process/cgroup swap;
the selected closure peaks at 3,823,976 KiB. Exact commands, revisions,
features, resources and #print axioms are in the JSON and selected receipts.

The first semantic launch was refused before Lean because an unchanged
prerequisite was absent. The pinned existing finish cache was reused and two
small pointwise canonicality targets were compiled. The finish theorem body
is exactly the existing ActualFinishAlphaSelectedCanonical pointwise proof,
with qualified aliases; its unrelated selectedAlpha packaging dependency was
not needed. Failed source drafts and refused-launch evidence remain retained
and are not selected as proof results.

The source checker pins the actual scalar and powers bodies against frozen
production, and the exact verify_observed, verify_finish and nonprover
semantic-rounds function bodies against their existing source kits. The
inherited original-source/compiler/runtime admission remains explicit. This
work derives source entry invariants; it does not by itself assert a new
whole-transaction equivalence theorem. The root composition consumes it.
