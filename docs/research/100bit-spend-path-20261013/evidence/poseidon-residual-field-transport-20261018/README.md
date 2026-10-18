# Existing Poseidon residual family across fields

Four checked generic lemmas preserve the existing R0P Poseidon scalar residual, its four-lane packing formula, and the complete residual list across any field homomorphism. The source and target openings use the maintained mapOpenings; low selectors, the block selector and their ordered folds use the existing field-transport lemmas. Public arguments are irrelevant to this particular family. This does not introduce a replacement relation.

The proof reuses PoseidonPairMap and the earlier Path/Value family transport for selector sums and openings. Nonlinear rounds remain opaque. Preserving the packing formula does not assert injectivity of packing on unrestricted extension-field values, and does not turn a packed zero into an unpacked zero. These are algebraic predecessors for the actual projected semantic caller, not membership, soundness or privacy theorems.

The focused Lean 4.32 check passed with four standard-only axiom reports: exit0,14.67seconds, peak RSS2,858,860,544bytes, process swap count0. The receipt records exact source revision, compiler, source/import hashes, command, LEAN_PATH and aggregate memory observations. No dependency or package-wide build ran.

Rejected v1 is retained. All structural field transports succeeded but left definitionally equal mapState functions in two notations. V2 closes those alias equalities explicitly with reflexivity, without unfolding a round or concrete recurrence. Full source/runtime/cryptographic and privacy obligations remain open. No production source or runtime artifact changes are made here.
