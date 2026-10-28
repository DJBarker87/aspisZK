# D370 state reconciliation

Recovered at 3ba01cb05b in the exact assigned worktree and branch. No prior
job was rerun. RECOVERY-D370.json inventories the host receipts and verifies
all available corresponding local hashes. Host completion records cover only
50300, 50301 and 50302; no L2C process remains. The allocation has charged three
Lean attempts (two failures, one pass), zero new Kani, leaving 97 Lean attempts.
Next focused ID is 50303; 50397–50399 remain reserved for final audits.

The native compiler-only probe's receipt and retained main.rs.txt are the
executed source. The current main.rs has additional masking/prover checks
which have not yet run. Its previous compiler-only evidence is not credited
as a reached guard counterexample.

The untracked integ4-source-availability.json is a read-only host comparison:
seven source files differ or are absent; it is not a native binding. The
untracked d369-native-view.py was replaced before execution with a minimal
plain-rsync helper. The private view links unchanged host files and overlays
seven differing/missing files, including the exact tracked host_terminal_field
source, using rsync. All 437 selected source/manifests/assets hash-match this
worktree; the base files were verified unchanged. No encoded payload remains.

The next diagnostic adds masking and a reached native semantic guard check on
the existing successful-preparation example. This is a changed probe, not an
unchanged replay. If it establishes the instructed honest-input counterexample,
the explicit counterexample stop takes priority over spending the remaining
compile budget. Otherwise the guard proof work continues.
