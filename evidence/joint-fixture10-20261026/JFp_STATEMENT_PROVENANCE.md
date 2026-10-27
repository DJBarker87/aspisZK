# Before/after statement provenance

The complete Rc10 source was captured before proof work and is byte-identical
at completion. Both successful kernel audits082 and100 loaded the same Rc10_Top
object hash (JFp_LEDGER_DELTA.json).082 used the default deep-term display and
its raw printed rendering had elisions; it is preserved in
JFp_082_RAW_Rc10_KERNEL.txt.100 enabled the supported pp.deepTerms display option
(no kernel depth/heartbeat change) and printed the deeper statement.
The BEFORE and AFTER kernel files therefore use100's rendering of that SAME
unchanged object; this is a same-object reconstruction, not a claim that082
printed the deeper text. Bound proof terms may still be omitted by Lean's
ordinary proof display. The complete mathematical source statement is retained
separately in both source files. No theorem/carrier/event/guard changed.
