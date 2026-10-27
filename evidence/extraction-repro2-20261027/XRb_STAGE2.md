# Isolation, comparison and budget boundary

6/6 Aeneas invocations, 0 Charon, Lean 0/100, Kani 0/0. All terminal. No additional extractor invocation is permitted. Exact release extraction has NOT succeeded.

| Attempt | Input / change | Exit | Wall s | RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| XRb_001 | exact release LLBC | 2 | 18.869505 | 220000 | 0 |
| XRb_002 | same release LLBC, Translate trace | 2 | 32.561094 | 228284 | 0 |
| XRb_003 | diagnostic masking, orphaned hash-cons keys | 1 | 0.919056 | 103752 | 0 |
| XRb_004 | expanded hash-cons references, root only | 0 | 2.587626 | 181424 | 0 |
| XRb_005 | root plus Prepared.new | 0 | 3.478969 | 181160 | 0 |
| XRb_006 | only compact.check_values opaque | 2 | 19.902760 | 232672 | 0 |

XRb_002 isolates the original Not_found to compact::check_values. XRb_003 is my diagnostic-construction error: removing function bodies orphaned global hash-cons definitions (Hash-consing key not found). Its input is excluded. XRb_004 first expands those references, then replaces unrelated bodies with Opaque; it translates root tx1. XRb_005 additionally preserves Prepared::new and succeeds. These two successful outputs are strictly DIAGNOSTIC partial extractions, with explicit masked IDs and hashes. They do not discharge child interpretations or certify the exact release LLBC. No tool or shipped source is patched.

XRb_006 starts from expanded release LLBC and masks ONLY Fun26 compact::check_values. It fails next at verifier::echeck, with InterpJoinCore.Distinct("Could not find a matching abs in right environment"), through InterpLoopsFixedPoint. Thus merely bypassing the first failure would not complete replay. Neither failure is a timeout or memory kill. No cap change or unchanged failed-run retry occurred.

XRb_declaration_diff.json and six .diff files compare historical raw extraction, actual selected union Types/Prepared-only Funs, and explicitly diagnostic output. Exact release output is absent and is never substituted by the partial outputs. Eight historical/release Rust quote pairs are retained. See XRb_Diff.md for interpretation and outstanding equalities.

Every attempt has full command, source revision/hash, dependency identity, exit/wall/process RSS/cgroup peak/swap/actual caps, raw errors and N/A axioms receipt; existing runner is unchanged. Reservation logs precede transfers, allowed=true, zero barrier retries, one scope at a time. No Lean theorem exists, so no #print axioms is claimed. Actual top/ledger unchanged, delta T0/P0/G0/C0; no new joint non-vacuity witness. Target not yet established.
