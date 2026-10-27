# Charged Kani run summary

Bounds and exact commands are in each target.json and harness.rs.txt. Toolchains and source/dependency hashes remain separate from deployed ELF/RunJoin association.

| run | exit | wall | reported peak KiB | swap | verdict |
|---|---:|---|---:|---:|---|
| kani-op34-exact-002 | 1 | 0:00.05 | 35176 | 0 | REJECTED; no equivalence verdict |
| kani-op34-exact-004 | 1 | 0:04.79 | 533448 | 0 | REJECTED; no equivalence verdict |
| kani-op34-exact-006 | 0 | 0:19.19 | 484740 | 0 | PASS (bounded harness only) |
| kani-op35-exact-002 | 0 | 0:03.29 | 419576 | 0 | PASS (bounded harness only) |
| kani-path-borrows-001 | 124 | 3:00.34 | 15468 | 0 | TIMEOUT; no verdict/counterexample; wrapper RSS excludes killed descendants |
| kani-pathbuf-borrows-r01 | 0 | 0:01.23 | 175380 | 0 | PASS (bounded harness only) |
| pop-owned-first-r01 | 1 | 0:01.69 | 296168 | 0 | REJECTED; no equivalence verdict |
| pop-owned-qualified-r01 | 124 | 3:00.31 | 15300 | 0 | TIMEOUT; no verdict/counterexample; wrapper RSS excludes killed descendants |
| pop-coordinate-r01 | 124 | 3:00.53 | 14944 | 0 | TIMEOUT; no verdict/counterexample; wrapper RSS excludes killed descendants |
| path-join-string-coordinates-r02 | 124 | 3:00.32 | 15476 | 0 | TIMEOUT; no verdict/counterexample; wrapper RSS excludes killed descendants |

Charged: 10/10. Refused admissions are not charged. No stubs or force-soft substitutions were used. No checked ROW counterexample was obtained. `#print axioms`: N/A native runs; exact revisions are in each collected-receipt.json. Native array, SHA2-vendor and block-buffer-vendor harnesses were prepared but never run.
