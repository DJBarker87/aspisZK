# S9 actual M31 primitive source bridge

This packet proves that the transparent generated M31 reducer/multiply/add/sub bodies in the pinned QM31 source cut align with the retained scalar cut and R22 wrapping model. It does not prove the still-opaque WideExact operations, complete QM31 multiplication, source-to-binary refinement, or runtime behavior. The actual QM31 extraction source cut is linked in `extraction-reference.json`.

The main bridge uses generated actual source bodies, not callback premises. For M31 add/sub it proves the exact wrapping expressions generally, then proves equality to the checked source operations under canonical operand bounds. Dependency owner builds are recorded as compile-only; the main theorem's transitive `#print axioms` audit is the trusted result.
