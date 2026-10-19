# Concrete RR runtime states and polynomial interpretation

Source base: abe6b03b235eba672556a6b53a884e208797900c. Four focused Lean 4.32 targets passed, with exact commands, source/import pins, exit status, wall time, process RSS, swap and axiom reports in the target evidence directories. Existing compiled dependencies were reused; no package replay was run. All printed theorem reports contain only propext, Classical.choice and Quot.sound.

The runtime list/drop normalization reconstructs exactly the normalized mathematical child, assuming the explicit degree, vanished lower slices and normalization-index bounds. RRConcreteState defines the dense-row state, executable scalar polynomial, zero-column polynomial, zero test and Option normalization. RRConcreteStatePolynomialView proves that the scalar polynomial is Q(0,Y), and that the executable zero test is true exactly when Q(X,0)=0.

This removes the abstract terminal-test premise when these states are connected to RR traversal. It does not yet discharge normalization success, preservation of Valid, concrete child mass and root descent for the full traversal. Those are the next bridge. The complete extractor, bit sampling, global cost, cryptographic composition, source/runtime refinement and 100-bit spend theorem remain open.

The dense-row algorithm is represented in Lean; this is not a proof of equivalence to a deployed Rust artifact. The compile evidence checks exactly the frozen sources copied to lean/. Each source revision is the pre-publication base in its receipt; source hashes identify the added files exactly.
