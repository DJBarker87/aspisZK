# Own-adapter documentation correction

The receipted PV_LIB_SLICE_TypedDrop source header says "at its own completion,
before return administration." That description is too strong. The actual
formal statement is advance3 of TypedDestructor.state0 = state(finalStore)3.
The provider's body has FOUR nodes: StorageLive0, aggregate unit, StorageDead1,
Return0. state3 retains body.drop3=[Return0], with no completed result yet.

Correct description: "the exact three-instruction typed-f22 prefix, preparing
the Return node, with its proved source-store frame and source178 selector."
No formal theorem, domain or machine is changed. The old source bytes are
retained as the accepted focused receipt's exact input; this correction applies
to all reporting and map qualifications. The unchanged proof is not recompiled
for a prose correction. This is not a frozen-spec correction.

This prefix graph does NOT install the full runtime-Drop/source178 suffix,
discharge f7's pending f6 dependency, or close a row. typedDrop178 stays MISSING.
