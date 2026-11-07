# NNF integration

Use the actual imported `TAS_Interfaces` types, not a copied interface.

```
let I' := NNF_TAS.install I
have dispatcher : RSL.TAS.NMW_Roots L D V0 VL P C I' :=
  NNF_TAS.roots L D V0 VL P C I
```

`install` retains every other Impl field definitionally. Both dispatch fields are the interpretation of NMW's freshly emitted bodies: `NNF_Reify.process_source` on admitted process inputs and `NNF_Reify.entry_source` on every entry input. The reification is a byte bijection and exact program/account/data reconstruction; no hash-based or projected input identity. Physical Rust slices supply the length bounds used only in these carrier lemmas. RowSpec folds themselves require no new length clause.

Four named full folds: `NNF_Folds.process_tx1` →333; `process_tx2` →221; `entry_tx1` →330; `entry_tx2` →213. Each process fold takes BOTH canonical wrapper RowSpecs because the frozen bodies are identical and cover both admitted routes. Each entry fold takes its process RowSpec and covers rejected instructions too. All four quantify over arbitrary V2Lib. The exact TAS fields are `NNF_TAS.r221/r213`; `roots` constructs the real structure, checking the field types in the kernel. The two row pairs are definitional aliases in canonical RSL.

`NNF_TAS.weak_process/weak_entry` demonstrate G1b with `RSL.TCK.weaken V0 w`; weak_entry has no Root0 or entry-domain hypothesis and retains only the full wrapper packets. Nothing equates the actual stage2 wrapper to the canonical model off Root0. Canonical Root0 occurrence binding remains G1c/top; this job neither supplies nor assumes global Root0.

Do not replace an independently chosen arbitrary I.process/entry by install without a semantic representation proof. The top can instead define those fields using this emitted interpretation initially; the remaining actual child functions keep their existing fields. A distinct physical adapter's correspondence remains its own obligation.

To instantiate a process root, apply its fold to actual candidate/CLOSED344 and240 at SAME arguments; instantiate the matching entry fold with that process root. NMV has no candidate wrapper roots at the final immutable read-only snapshot, so these remain complete parameterized folds, not row-credit claims.

Export and replay paths are in NNF_EXPORT.json and NNF_ENV.json. Import NNF_COMBINED_IMPORT for the focused ledger24 plus NNF closure. The raw own-root audit covers the23 proof theorems listed in NNF_AUDIT_ROOTS.json; existing ledger roots are not re-audited. No shipped edit, ELF rebuild trigger, trust-row change, or release claim.
