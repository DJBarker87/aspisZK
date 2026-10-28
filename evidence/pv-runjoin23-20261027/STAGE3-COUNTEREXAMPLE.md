# Checked stop: Admission does not fix cached compiler payloads

`PV_RunJoin_AdmittedReturnCounterexample23.universal_guarded_return_false` checks in attempt38120. For every K : Type with [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647], it proves the full statement:

```lean
¬ (∀ i : PV_Src_NativeInput.Input,
    PV_RunJoin_UniversalBuild22.Admission (K := K) i →
    PV_Src_RecordReference.Checked i →
    (∀ l : Fin 20, R0Z.WriterRefine.Canon8 i.snapshot.frontier.val[l.val]!) →
    @PV_Src_NativeInput.run PV_RunJoin_ShippedExternal.E_shipped
      PV_RunJoin_UniversalRecords22.shipped i = Aeneas.Std.Result.ok (.Ok i.compiled))
```

This is the precise compiler-return/association hypothesis that UniversalBuild22.build_eq requires, strengthened by all its remaining primitive word/frontier guards. It is false even on the explicitly admitted subtype (`admitted_carrier_return_false`).

## Exact input and checked facts

`counterexample := PV_RunJoin_PayloadAssociation22.altered PV_RunJoin_AdmittedCarrier23.transfer`.

The underlying transfer is the literal original fixture request, witness, transfer change, lane anchor, snapshot and actual TransferPayload20.output. The only update is `compiled.trace.variant := flip compiled.trace.variant`, changing PrivateTransfer to Withdrawal. All compiler arguments, the compiled public statement, public projection and merged columns are preserved. No shipped source is changed.

The accepted module proves separately:

- `admitted`: semantic Admission for this exact input (not conditional on a hypothetical admitted fixture).
- `checked` and `frontier`: actual primitive range/canonicality guards for this exact input.
- `actual_return`: the original compiler call still succeeds, returning the original transfer payload.
- `not_cached_return`: that returned payload is not this caller-supplied cached payload.
- `universal_return_false`, `universal_guarded_return_false`, `admitted_carrier_return_false`: the corresponding universal derivations are false.

The earlier fixture bridge38118 proves both concrete inputs admitted for every specified K and proves both original successful compiler returns. Their witness association uses the named TransferWitness20/WithdrawalWitness20 model equations and `model_injective`; no whole run/hash/bank recurrence is reduced. It proves universal public equality on the explicitly declared admitted subtype, with `nonempty_both` providing both fixtures. This does not change the original raw source domain or remove V152.

## Scope and stop

This is a counterexample to the requested universal compiler-return/association step, **not a checked counterexample to V153's raw-trace equality**: the mutated variant does not change the merged columns. It is also not a counterexample to compiler success expressed merely as existence of some returned output: `actual_return` proves that existence here. The failed universal law is specifically success returning `i.compiled`, the hypothesis in the existing universal build proof.

Under the current prompt's explicit rule, “a universal step false for some admitted input is a checked counterexample and a stop,” proof progression stops at38120. No replacement domain, success guard, payload association hypothesis, bank certificate or new T field is silently introduced. V153's universal bank validation/carry/reconstruction is not asserted; the existing iff between aggregate success and all57 blocks is retained at its prior scope. V154 is not newly discharged. UniversalBuild22.transport_eq already identifies the fixed extracted transport with D18 as equality of the full Fin1024 equivalences; this unchanged reference theorem is audited/reused, not promoted into a new deployed-source closure.

Attempt38119 is retained as a failed candidate: a Checked proof indexed by the original Input does not directly inhabit Checked of the modified Input. The replacement38120 reconstructs the five primitive proof fields explicitly. Its entire module passes, with only propext/Classical.choice/Quot.sound, peakRSS4,984,000,512bytes, swaps0. The earlier partial axiom lines from38119 are not accepted as standalone proof evidence.

Recount6:407 rows; OPEN86; CLOSED-ON-CANDIDATE44. Whole rows removed0, including V038/V045/V047/V152–V154 retained. Endpoint premises removed/added/weakened0/0/0. Deployed P OPEN→OPEN; constructed P and records2/8/6 unchanged. T remains exactly entropy_law,entropy_kernel,observation. Privacy target not yet established.
