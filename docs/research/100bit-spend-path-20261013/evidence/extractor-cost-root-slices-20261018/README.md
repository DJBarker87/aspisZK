# Extractor cost and Roth–Ruckenstein slice checkpoint

These are focused mathematical proof results, not a completed efficient extractor or a 100-bit soundness release. The next work attacks actual decoder extraction and the algebraic decoder runtime/completeness gaps. Routine caller import rebuilding is parked. Elapsed task time reported by the user is 2 days 13 hours, not a week.

## Proved

- `MerkleRecoveryCost` instruments the existing executable finite-log Merkle recovery functions, proves identical returned values, and bounds digest equality tests. Three batches of at most 262,144 paths, depth at most six, and node/leaf tables of length at most Q require at most 5,505,024 Q comparisons. Here Q bounds record-list length, which can include repeated reads; it is not silently identified with the soundness theorem’s distinct-first-read count.
- `FiniteFieldModularPower` proves the binary-recursion modular exponentiation result has the correct polynomial remainder.
- The complete-root certificates prove both directions of root membership and the degree cap. Checking only that returned elements are roots would not establish completeness; the gcd certificate supplies that missing direction.
- `RRRootMultiplicityTaylorV3` proves the Hasse/Taylor coefficients below root multiplicity vanish, and the coefficient at that multiplicity is nonzero, in any characteristic.
- `RRChildSliceTaylorV4` gives the explicit Taylor-convolution slice and its degree bound.
- `RRChildSliceMultiplicityV3` proves a nonzero slice exists with index and degree bounded by the multiplicity of the chosen root of the parent’s constant-X slice.

The RR degree bound concerns the first nonzero X-coefficient slice after substitution. It does not bound the Y-degree of the entire bivariate child polynomial.

## Not proved here

The root-certificate modules use mathematical polynomial/Fintype operations in a noncomputable section. They do not supply an executable factorization algorithm, polynomial operation-cost theorem, or randomized failure bound. A uniform executable implementation must take the explicit field cardinality q as input with a correctness proof, rather than enumerate the field to obtain `Fintype.card`. The selected decoder field is WideExact (approximately 248 bits), not QM31.

The correspondence between these coefficient slices and actual normalized bivariate substitution, the RR tree invariant, interpolation construction, complete root factorization, and full extractor refinement are open. No dense interpolation computation was executed. The two newest RR modules did not print axioms in their focused receipts; the next changed consumer must print the transitive axiom report before a formal release claim about them.

## Evidence and provenance

`manifest.json` lists source/object hashes, exit statuses through individual receipts, wall times, peak RSS, process swaps and available axiom reports. All seven accepted focused compiles exited zero with process swap count zero. Existing host swap usage is separately recorded and is not claimed zero. No package-wide replay was run. The unchanged Merkle dependency source snapshots and focused failed-attempt history are archived. Runner scripts and command/import pins are retained.

Root’s recovery receipt records source revision 1a39ad608. Query’s receipts record its working checkout revision 700dd4b4, not the integration branch HEAD. These uncommitted-source compiles are identified by their exact frozen source hashes; they are not represented as whole integration-checkout builds. The seven source files integrated here are byte-identical to the successful snapshots. Existing cache objects were reused; this checkpoint is not a full frozen manifest replay.
