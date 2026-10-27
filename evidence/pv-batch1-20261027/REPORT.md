# Batch 1 stopped at gate (a)

Branch `codex/pv-batch1-20261027`, base `c57a344726745387efb38d1571d885c69ce829ee`, applied revision `138cf2cf7d`. Target not yet established.

## Applied source

Only route2 patches230,254,258 were applied, following independent `git apply --check`. Seven Rust files,28 additions/9 deletions. Op230 adds the prover-local sum and redirects host_semantic, prover and sim;254 changes the final-iteration branch;258 changes iterator scans into indexed loops. `applied.diff` includes the new helper file. The sole mechanical adaptation moves the host_semantic import below the existing inner module doc comment. Op223 unchanged.

## Mandatory stop

Default verifier rebuild completed successfully but FAILED byte pin equality:

- Expected/baseline: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,1,563,728bytes.
- Actual: `46ea9c91b66b40d02f21be23c6a2effeb69dba91ae0e2ab7f50094882c246a22`,1,563,776bytes.
- 803,305 differing positions within the overlapping byte range;48 trailing candidate bytes. Exact first64 positions retained in `byte-difference.json`. This is a raw binary comparison, not a semantic diagnosis.

Target: `programs/r1-cost-probe/Cargo.toml`, features `pool-adapter,private-leaf-salts`; full command/environment in the receipt. Exit0,wall36.116s,peak686,024KiB RSS,swaps0,source`138cf2cf7d7a606f20be31f357a137fc07b4fad0`,`#print axioms`:N/A(no Lean). Scope limits6G/8G/swap0/Tasks64. The comparison wrapper exits1 on mismatch.

Stopped immediately: no devnet or Pool build, extraction, Lean compile, source-law proof, port nonfailure proof, native client build, fixture comparison, full manifest or final axioms audit. No source counterexample was checked. The gate failure is not repaired or bypassed.

## Proof and premise status

V247/op230, V261/op254 and V264/op258 complete arbitrary-input Result/source laws remain OPEN. The original-row sum bridge, arbitrary-N powers bridge, pole verdict equivalence and every backend shift-port nonfailure proof remain OPEN. No theorem was added and no proof claim is made from source inspection.

Before/after: endpoint `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its deployment premises unchanged; removed0,added0,weakened0,changed0. T remains exactly entropy_law/entropy_kernel/observation. E1/E2, actual RunJoin, client identification and L1/L2/L3 are retained. Combined1,000-run differential/timing remain the lead’s gates.

Budget unused by explicit stop rule:0/100 Lean,0/0 Kani; no env-J ID consumed; next53600,final audit53897–53899 unused. No local Lean job or shared env-J write.

Next concrete deliverable: lead review of the default ELF byte mismatch, build command/environment and changed-source reachability, followed by an explicit decision before resuming adoption. Three source patches remain committed for review; no push.

All receipts and raw first64 byte differences were collected after fresh successful reservation admission. Generated program keys were retained mode0600. No binaries or key material are committed. Python syntax checks and source-diff whitespace checks passed. The collected raw metadata-failure stderr contains trailing whitespace; it is preserved verbatim and the staged whole-evidence whitespace check reports it. The initially committed applied.diff omitted the then-untracked helper; the final applied.diff is regenerated from the committed source revision and includes it.
