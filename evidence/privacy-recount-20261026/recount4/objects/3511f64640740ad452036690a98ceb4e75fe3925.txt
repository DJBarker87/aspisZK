# Withdrawal: same exact missing source-leaf association

No actual selected Input term has been constructed. The recorded public and
full transition terms are `PV_RunJoin_RecordedWithdrawal.publicRecord` and
`.transition`, from the pinned withdrawal bytes. No compiled payload is supplied
as an arbitrary parameter and called an actual compiler return.

The exact missing proposition, with R_shipped/E_shipped and w/snapshot defined
as in stage1-missing-fact.md at the withdrawal invocation, is:

```
Records.call R_shipped w 250#u32 none change snapshot 77#u32
  = @PV_Src_RecordDynamic.call E_shipped
      w 250#u32 none change snapshot 77#u32
```

Change is exactly owner lane i = 701+17*i, salt lane i = 801+17*i, value 750;
the source withdrawal public has amount 250 and destination [6;32]. Shipped
locations: r0_fixture.rs:105–149 and pair_forest_trace.rs:442–488, calling the
same records leaf at pair_forest_copy_builder.rs:227–270. This is a precise
source-association statement, not a compiled theorem: the source boundary has
no identified concrete R_shipped Lean constant in the supplied closure.

Stop this stage at that missing fact. Compiler-return, full public association
and public binding remain OPEN. Stage 3 runtime/observer installation and
P ∧ T non-vacuity remain OPEN for both fixtures with T hypothetical. Stage 4
(the 11 L2 objects and trace) has not started, as its prerequisites are not met.
No ROW counterexample was checked or claimed. No T field was added; A/B remain
unadopted. No endpoint premise was added, removed, renamed or weakened.
