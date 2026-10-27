# Actual retained proof: complete extracted shape and canonical scan success

`JFz_ScanAccepted.source_accepted` proves:

```
Op4P_Install.sourceBody JFx_NativeBytes.proof = ok (.Ok ())
```

`JFz_ScanAccepted.shape_and_scan` joins it with the existing op3 success on
THAT proof. `scan_accepted` covers all 47 exact regions, including both
non-salt fields of all 22 openings. This is a forward sourceBody success
result; no accepted native caller/cut is a premise. The 13 additional compact
semantic payloads are also checked, one word at a time, on the retained bytes.
Their source/data hashes and offsets are in JFz_SCAN_MANIFEST.json.

Focused validation: JFz_005–064 passed for the 60 region modules; JFz_097
passed the composed scan/shape endpoint. Standard axioms only. JFz_094 failed
because a Slice metavariable was not inferred from a list-length theorem;
JFz_097 supplies the explicit proof Slice. No full caller was reduced, no
limit was raised, and no package replay ran. Exact receipts are retained.

`JFz_RowGeometry.forward` (JFz_096) proves one forward semantic parser step,
with physical list slicing identities. JFz_065 failed on a missing import;
JFz_066 failed on a length conversion and unspecialized branch hypotheses;
JFz_096 normalizes those hypotheses and supplies the named length fact.
None of the failed outputs is accepted proof evidence.

The actual top remains byte-identical. This stage supplies an open fixture
subgoal, not the complete joint execution. It removes zero actual-top premise
families and does not assert either SDK wrapper accepts.
