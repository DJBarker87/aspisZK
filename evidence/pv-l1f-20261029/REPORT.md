# L1F count link discharge — D472

Work in progress. Branch `codex/pv-l1f-20261029`, base `e22474ea34`, exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-l1c`.
Target not yet established. All frozen L1E Link definitions remain unchanged.

Budget: 100 Lean starts (67100–67199, audits 67197–67199), at most 20 native scopes, zero Kani.

The new returned-count module reads the actual extracted RetriedProof.attempts.val and consumes pv-diag2's finish_result. This readout is separate from acquiring the complete ordered count/rejection history.
