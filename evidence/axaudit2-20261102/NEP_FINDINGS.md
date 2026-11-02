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

## Stage B: visibility hardening and limits

The release entry point is `NEP_Driver.lean`, executed with `lean --run`.
It explicitly imports all requested modules into one environment with
`importAll=true`, `level=.private`, and initialized extensions. The raw
`NEP.audit` uses only checked kernel types and values (including opaque values)
and constructor edges. Imported summaries enter only the subsequent equality
comparison. A missing reachable name logs its root, parent and partial sizes,
then throws; no skipping, filtering, imported-summary substitution or invented
matcher declaration occurs.

`NEP_R024` passes eight standalone cases: four planted axioms and four matched
axiom-removal mutations. The reachable files include the actual match_1
auxiliary, private secret, opaque theorem body dependency and hiddenAux.
Each original reports its one axiom; each mutated body reports no axioms.
All eight results equal collectAxioms and actual #print axioms output.
`NEP_validate.py --stage-b` passes receipt, pin, reachable-set, mutation and
negative validator controls. `NEP_R025` recompiles the final walker; its raw
traversal is unchanged from R024. The removed experimental nested-import API
is not the release entry point.

Explicit private loading does **not** resolve the real cohort failure:
`NEP_R023` exits 1 without a panic, after 1,910 discovered constants and
25,955 scanned edges, at the same direct source-to-matcher edge. Both involved
legacy .olean files have no server/private companions in the copied cohort.
Full kernel lookup, full elaborator lookup, serialized-table inspection and
private-level reimport agree on absence. Thus the exact immediate obstruction
is a serialized theorem referring to a declaration not supplied by this
closure. Rebuilding/reconciling its producing dependency is required before a
complete raw audit of that root can succeed. A loading-only correction cannot
establish completeness for an absent declaration. The historical compilation
cause (including whether an object mismatch or a serialization problem produced
it) remains unestablished; no repair of a frozen proved module was attempted.

Preserved implementation errors: R001 lacked noncomputable annotations; R006
used an import-all line the runner scanner treats as a module named `all`
(no Lean started); R014 lacked initializer enablement; R015 required an unsafe
loader declaration; R022 had a record indentation error. R021 additionally
exposed an invalid-extension panic after restoring a pre-initializer command
environment; the standalone R023 driver eliminates that lifecycle problem.
These were own-source/input problems, not lead-owned launcher modifications.
All 25 focused scopes (counting R006 conservatively) remain within the budget.
Admission used the unchanged agg16 reservation scanner conservatively for
16 GiB even when the actual scope cap was 8 GiB. All admissions allowed=true
and exit 0. No refusals, transport retries or cap raises occurred.
