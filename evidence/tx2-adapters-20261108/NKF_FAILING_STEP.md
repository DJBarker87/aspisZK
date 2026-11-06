# Exact failing steps and replacements

Target not yet established. Historical failures and sources remain retained.

* K081 was submitted ONCE after host repair: admission exit0/allowed:true,
 129497116672free bytes; source-erasure/offline-frozen-graph checks passed and
 Cargo.lock unchanged. cargo-kani0.67.0 invoked rustc, which failed creating
 NKF_tmp/rustcnaCM0r: No such file or directory. Prior owned end cleanup removed
 NKF_tmp, and the resumed submission did not recreate it. No CBMC assertion ran.
 Final native allowance consumed; no resubmission, no negative-control credit.
* K064 iteration and K067 constructor inverse are retired TIMEOUTs. New Lean
 factorizations L018/L022/L031 pass; exact future native windows/control plan
 is NKF_SPLIT_PLAN.md. No timeout/cap increase or unchanged native retry.
* L017/L019/L020/L021/L023/L030 are excluded failed drafts; error-recovery
 sorryAx in failed outputs is not accepted. Fresh changed-source L018/L022/
 L031 pass and raw ax2 sees standard axioms only.
* Joint orchestration initially read a predecessor path omitted by sparse
 checkout. Read exact committed blobs by git show with SHA validation; reused
 L024/L025 without replay. No proof scope was lost to that local parser step.
* L026 link failed because owned TMPDIR was absent. L033 adds retained
 NKF_tmp/.keep and links successfully. This repair never reruns K081.
* L032 pin script expected inherited lean-toolchain/S2W_lean_host inputs that
 this workspace does not use. L035 pins actual LEAN_SYSROOT lean/lake/leanc,
 lakefile.lean and the actual S2W_run_host launcher; comparison remains strict:
 all32556predecessor files must match. Exit0, zero mismatches.

Historical K046/K050/K062/K063 compile failures, K065unpaired inverse,
K066unpaired pass and K080control-order bug earn no native credit.
