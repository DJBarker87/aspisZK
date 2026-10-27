# Exact remaining installation facts

No T field is added. Options A/B remain unadopted.

For the proof-account caller's SAME selected input i, source compilation must satisfy
`@PV_Src_NativeInput.run actualExternal actualRecords i = .ok (.Ok i.compiled)`.
For each endpoint witness w with h.public w = x.1, selection must satisfy
`PV_Src_NativeInput.publicInput (selected h x w) = PV_Src_NativeInput.publicInput (publicRecord x)`.
The right side includes the compiled public_statement transition. No arbitrary compiled value may be substituted.

The published `PV_Src_FrozenPublic.correspondence` retains compile success and uses owned reference dictionaries. `PV_Join_FixtureSelected.both_source` retains the selected-record function and proves BodySourceLaw; `PV_Join_FixtureInputs.same_record` preserves that SAME input and compiled record. None supplies the two facts above for the deployed fixtures.

Transfer and withdrawal each additionally need actual compiler dictionaries/returned selection, admission, world/policy/body initialization, the native callback/store/carrier association, complete disclosed/oracle decoding, and the unchanged outside-bad-event extracted trace equality of TrustEndpoint.ProofObligations.trace. A generic Runtime construction with arbitrary missing data is not a concrete deployed fixture.

`PV_RunJoin_TrustFixtures.both_fibres` supplies mathematical witness fibres and separate T models, not deployed P∧T. The old empty-native-log obstruction remains conditional on an exact successful source coin; it is not a checked ROW counterexample.
