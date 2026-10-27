# Finish laws baseline

Target: AspisR1.Rc3_Top.deployed. Baseline revision recorded in SAF_001.json.
Assigned scope: SAF_ new modules only; existing sources/candidates read-only.
No shipped change, no ELF rebuild trigger, no Kani invocation.

Ledger baseline: 82T+113P actual; Session A 92P = 28 finish laws,
3 primitive returns, 61 separate binding laws. This job targets the 31 finish
and return rows, not the concurrent SAQ binding rows.

Installed parent normalizes release tracing, comparison and fold count, but
Configuration.finish remains data-only and abstract. FinT gates transport
PairingLaws rather than deriving concrete instances. Session A S5 returned
residue decoding requires withConcreteDot/finishConcreteField/QRaw;
S3 grouped-loop lift requires local source-step meaning; S4 zero-scanner
all-input equivalence is about indexed/tail SDK scans, not match0. None can
be silently specialized to an arbitrary Configuration.finish.

Planned first removal: invert the actual accepted Port4D finish return already
present in Cons_Native.Calls. Construct both RoundValues and the same actual
weights/pair/dot returns. Specialize only those output-dependent operands,
retaining all semantic laws and common source/model witnesses. This must be
composed to a new top before receiving ledger credit.
