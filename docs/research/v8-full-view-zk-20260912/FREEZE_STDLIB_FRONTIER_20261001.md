# Freeze source frontier, 2026-10-01

This [diagnostic bundle](evidence/freeze-stdlib-switch-global-20261001/manifest.json) records focused attempts to unblock the actual selected full freeze. It contains no new formal security claim and no replacement standard-library assumption.

The R160 input failed because slice fold reads the generic IS_ZST global directly in a branch condition. The retained Aeneas decomposition pass handled global reads in assignments/assertions/calls but skipped switch scrutinees. An isolated patched translator applies the same existing visitor to If, SwitchInt and Match scrutinees. The optimized cached build succeeded in 7.49 seconds; its actual enclosing container slice peaked at 803,975,168 bytes with zero swap. The selected Rust source was unchanged.

That translator advances the unchanged R160 input past the global-read failure, then stops on the opaque slice Iter layout. A fresh narrow extraction including Iter and NonNull layouts succeeds, but translation rejects the raw non-null pointer pattern type. A separate constant-evaluation attempt hits a missing initializer in FunsAnalysis. Full logs, commands, patch and checksums are retained. No failed job is repeated unchanged with a higher cap.

The saved full R156 freeze also needs an error-return audit: some nested residual branches discard the residual result and return `done none`, while the outer generated function maps none to panic. The pinned Rust source uses `?`, which should return the relevant error. This is a structural concern, not a proved reachable semantic counterexample. Two tiny standalone return-after-loop probes fail earlier at loop context matching; they are not selected-verifier source substitutes.

Accepted FunsCore excludes the full freeze, and the R171-R176 component proofs do not depend on those full-freeze branches. Before whole callback equality, prove the actual fold/extend operations and repair or justify error-return correspondence. Continue using the existing error-preserving SelectedResearchScheduleProgram; RelationPrefixCorrespondence.BridgePremise.exact remains unproved. Privacy and soundness remain open.
