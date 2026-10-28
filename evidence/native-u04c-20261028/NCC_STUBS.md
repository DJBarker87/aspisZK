# Stub and contract register

No field multiplication or SHA implementation is stubbed or unwound here.
There are no new field-arithmetic stubs requiring a Lean discharge. All field
arithmetic rules and the existing runtime digest trust remain unchanged.

All six prescribed KMX copy annotations use exactly
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67;
the actual stub bytes hash to
ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.
The inherited register is evidence/native-tx2j-20261028/NBU_STUBS.md:
KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame/append_spec/realloc_prefix,
NBU_CopyWindows and NBU_SourceWindows. These are reused via NBX's audits and
NCC_ReuseAudit. No custom copy implementation is used. Actual safe local slices
provide the range/length domains; no allocation path is credited by a copy law.

| Contract replacement | Callee proof | Domain / use |
|---|---|---|
| NCC_weak, True ensures | K036 | Full native V1 record; K038 is a deliberately unentailed caller control and receives no native refinement credit. K037 is its actual-body baseline. |
| VerifierRegistryV1::is_immutable, exact flags bit | K056 PASS | Full valid typed reference, requires(true); K059 PASS / K060 intended failing control, actual unchanged native validator. |

The false-ensures and wrong-modifies functions are never substituted as verified
callees. Their failures are machinery controls only. Prepared but unexecuted
entry/caller contract candidates receive no proof credit.
