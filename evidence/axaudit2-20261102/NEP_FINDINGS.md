# NEP walker completeness findings

Stage A: the Stream B missing matcher reproduces without the large combined import.
`NEP_R012` imports `JGx_SdkAfterValidationEq`, uses 4,384,244 KiB peak RSS,
and fails at the direct edge from `AspisR1.JGx_SdkAfterValidationEq.source`
to `AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3`.
Both checked-kernel lookup and full elaborator lookup return none; module lookup
also returns none. The serialized table contains no matching declaration.
`NEP_R011` independently scans the copied top-level serialized modules one at a
time. It identifies the same reference in the source theorem, two equation
lemmas and a splitter in `JGx_SdkAfterValidationEq.olean`. The owner of stage2
is `AdapterRwModel.olean`. Both files report isModule=false. The stage2 body
references match_1 and match_2, not match_3. Its own raw closure succeeds in
`NEP_R009`: 3,512 constants, 50,454 edges, the three standard axioms, equal to
collectAxioms. This is a dangling serialized dependency in this cached cohort,
not an asynchronous lookup discrepancy. The provenance of that dangling edge
needs further investigation; no claim about which historical compilation
introduced it is established.

Separately, `NEP_R003` demonstrates a module-system visibility hazard: exported
opaque definitions/theorems are represented as axioms in a restricted importer.
The raw walk sees the public root itself as an axiom and disagrees with the
imported collectAxioms summary. A legacy plain importer (`NEP_R004`) sees all
four planted axioms. `import all` alone (`NEP_R008`) does not repair the
checked view used by this test. Explicit private-level reimport is tested in
stage B.

The earlier NDP implementation aborts on an unresolved reachable constant and
on any mismatch with collectAxioms. These failures cannot silently yield a
successful under-reported raw result. Its completed historical walks remain
evidence for their exact recorded objects and roots, not for this different
combined cohort. An incomplete walk or imported summary alone supplies no
complete raw axiom set for the obstructed root. No nonstandard axiom has been
inferred merely from this missing declaration.

No protocol, theorem contract, frozen implementation, or cryptographic
assumption is changed by these diagnostics.
