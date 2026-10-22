# Prover commitment continuation 42

Work in progress. Target not yet established.

The task base is f57f0546d8af9a4355a3df1f8eaf91dc7a4e33c4 (the fresh
worktree supplied to this continuation). No shipped sources changed.

## Raw private domains

`ProverCommitRawFresh42` closes the unverified part-41 domain-separation
draft: all three raw seed families differ from both public bindings, and
outside `PrivateMemo40.guessed` they avoid the retained old history plus
both binding reads. The statement digest address remains a separate
obligation; no private-derived read bound is replaced by this result.

J9442 is a rejected draft (simplifier did not reduce `if True`);
J9444 compiles the corrected module: exit 0, wall 2.15 s, peak RSS
4,163,112 KiB, zero swaps. All three printed axioms lists are subsets of
[propext, Classical.choice, Quot.sound]. Exact source bytes, dependency
fingerprints, source revision and commands are in
`../../100bit-spend-path-20261013/evidence/prover-commit42-20261022/lean/`.

J9400 was refused because its receipt already exists for another module;
no compiler ran and its existing evidence is not attributed to this work.
A read-only range inventory identified available numbers within J9400–J9799.

## Selected generated owner

The unchanged generated Types/Funs from part 41 are now installed and
compiled independently (J9443/J9445), exit 0, standard generated definitions.
The semantic bridge is in progress; compilation alone is no refinement claim.
