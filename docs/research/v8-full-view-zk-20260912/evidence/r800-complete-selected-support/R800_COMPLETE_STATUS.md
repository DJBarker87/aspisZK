# R800 selected support characterization: compiled evidence

The source generator emits 53 modules, each covering at most four of the 212 non-prototype active source rows. Rows 114 and 1022 reuse the earlier green prototype. generate.py --check passes with the pinned table, mapping, input, and dependency hashes.

Each chunk compiled with exit status 0 using the pinned Lean 4.32 cached workspace, -j1 -M4500, and a separate 5 GiB/7 GiB, no-swap, 128-task systemd scope. The complete #print axioms output is retained in every run receipt and log. All reports contain only standard Lean axioms (propext, optionally Classical.choice, and Quot.sound).

These results prove the finite selected-column support characterization and the generic zero result for sourceChord outside each row support. They do not establish selected-verifier matrix equality, a rank statement, privacy, or soundness.

See manifest.json for every chunk source checksum, source revision, receipt/log, direct imports, pinned input files, time, peak RSS, swap, and complete axiom outputs. prototype-evidence/ retains the earlier prototype evidence including its failed first attempt.
