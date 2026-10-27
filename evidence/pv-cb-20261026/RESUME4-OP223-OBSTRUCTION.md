# Op223 / V240 current source binding

The existing `PV_CurrentScaleInstall.selected` does not update op223. The
rw candidate still requests an explicit `P_source_p6` binding from the original
callback dictionary to the extracted compressor reference. Its reference totality
and finite-loop lemmas are not that binding. No source law is published here.

Fresh sibling check: op223-sibling-check-resume4.json. No sibling source law.

Changed extraction routes (both retained, not rerun unchanged):

- `charon-source-op223-resume4-opt`: optimized MIR, Charon exit0;
  `aeneas-source-op223-resume4-opt`: exit2.
- `charon-source-op223-resume4-narrow`: built MIR with only exact compressor and
  lift inclusions, Charon exit0; corresponding Aeneas exit2.

Both fail with exactly:

```text
ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation
```

The preflight is not disabled, and no external-function template is installed.
These failures do not show the shipped ROW statement false. A model-only
callback-independence check is being compiled separately, not credited as a
source row or a checked shipped-source counterexample.

Next direct route: a supported iterator/reference extraction; next P6 route:
owned reference plus shipped=reference on the proved canonical calling domain.
The actual cost-probe caller obtains an Array M31 16 from copy_tuple_values,
then passes its Slice to op223 (ProverRwFullFuns host_semantic copy-values loop).
Any bounded native proof must be paired with the exact caller-domain invariant;
an arbitrary 16-element fixture does not prove the universal row.
