# Retained native bytes and compatible source ports

The retained transfer-13 triple is now literal Lean data, not just a hash:

| Carrier | Bytes | SHA-256 |
|---|---:|---|
| proof suffix | 57607 | 55386c507d3feeebfc45272a1cf15c33ccb9ccf0a8a8f41180fc654d806fff6f |
| physical ASF8 public | 1880 | f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331 |
| verifier checkpoint | 1768 | 6c9f774dd0032d3df18c9724c38d02c5225f31808a4cfe8560c210dc4d3dc625 |

Proof/public come from the retained format-adopt fixture files identified by
runtime-command.json. Checkpoint bytes were read from the retained build-host
file `/home/dombarker/project-offloads/pair-h5-adoption-native-runtime-v1-20261023/runs/readonly/2/runtime/after/checkpoint.bin`.
Its hash above is freshly observed; it is not described as an independently
historically signed hash. The other two hashes match the inherited runtime
input manifest. No key file was read, changed or removed.

JFx_NATIVE_AUDIT.json checks all 562 shipped source hashes and seven retained
receipt files; zero mismatches. This is reused native acceptance evidence, not
a new native run or a kernel accepted-source execution.
JFx_generate_data.py --check and JFx_DATA_READBACK.json independently validate
the generated literals against the retained byte hashes. No binary is committed.
The checkpoint can be regenerated from its retained literal source; an explicit
--checkpoint path can instead supply its original bytes.

Kernel-checked current results:

- JFx_NativeBytes: all three exact lengths and bounded Slice carriers.
- JFx_NativeHeader.first_sixteen and JFx_HeaderFields.shape_accepted:
  actual retained proof header/op3 acceptance, not full spend acceptance.
- JFx_FixturePorts.same_inputs / physical_ranges: same-carrier P2Prime,
  all six node ranges and the compact y1 input on these bytes. No hash
  injectivity, parser acceptance or successful scan is asserted.
- JFx_CanonicalExtraction.canonical: actual extracted source functions
  construct D188; no acceptance is asserted.
- JFx_SourcePorts.jointly: for ANY supplied seed configuration, ONE source-selected
  CPH dictionary supports D188 with actual extracted natives, preparation owner,
  query/geometry/domain owners, geometry mul/one/inverse, and P1/syscall model.
  This remains parameterized by the seed; it is not a closed accepted fixture.
- JFx_PortCompatibility.same_dictionary: that same dictionary equals the
  compatible Rc3 installation. This is not a claim identifying the different
  frozen2/frozen3 headline statements.

All final-source modules have a matching successful compile and printed axioms
in JFx_VALIDATION.json. Only propext, Classical.choice, Quot.sound occur. Failed
attempts, including their error/sorryAx output, are retained as FAILURES and
never used as acceptance evidence. All new sources compile at their final
hashes. No maxHeartbeats/maxRecDepth option, new axiom or proof hole is used.

Compilation stayed on the coherent SInt2 host workspace. Existing read-only
PAln/PSem caches supplied missing unchanged imports; source/object hashes are
pinned, and 60 matching PSem sources plus the PAln sources were checked against
this checkout. No existing module or launcher was edited. Only JFx_ host files
were created. For the last batches, one admitted scope ran separate one-file
attempts serially; every attempt has its own time/RSS/swap/source/dependency and
axiom receipt. Cgroup memory.peak is cumulative within those batch scopes;
/usr/bin/time peak RSS remains per attempt.

Failures and replacements: short import path -> retained CPP path; rfl128
literal lengths -> named symbolic 32-byte chunks and balanced append; reserved
public identifier -> publicInput; missing PAln/PSem objects -> read-only cache
paths; direct huge dictionary rfl -> CPH/Rc3 symbolic lemmas; header list/array
normalization -> explicit tiny take/index/Array.make lemmas. No timeout or OOM
was rerun unchanged. Caps remained High6G/Max8G/Swap0/Tasks64; Lean -M7000.

This stage removes ZERO actual-top premises. Full before/after statements and
atomic-law-family zero delta are in JFx_LEDGER_DELTA.json and the paired source
snapshots. No shipped source or cfg(kani) module changed; the three inherited
ELF pins were not rebuilt or reattributed.
