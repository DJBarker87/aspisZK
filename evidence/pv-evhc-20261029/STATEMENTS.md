# Exact frozen consumer statements

Source: `lean/PV_EVH_FixtureConsumer.lean` at `b51b1040f2ffda4a6370a15ea71e5783a16bfa11`, SHA-256 `2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4`. These are source statements, **not newly elaborated results**. Names resolve in namespace `PV_EVH_FixtureConsumer`, with the source's `open` directives.

### `public_fibre`

```lean
theorem public_fibre (handle : PV_RJ4IDB.Bytes) :
    ∃ w : R1Z.PV_RJDec_V047.H.Instance,
      R1Z.PV_RJDec_V047.H.public w = (deployedStatement handle).1
```

### `two_transaction_nonvacuity`

```lean
theorem two_transaction_nonvacuity
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second
        (AdapterRw.r1_pool_adapter.owned.stage2_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,()))
```

### `instance_nonvacuity`

```lean
theorem instance_nonvacuity (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      (deployedInstance base stage slot).1 =
        ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      (deployedInstance base stage slot).2.1 =
        ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val = JFx_NativeBytes.checkpoint.val ∧ saved.val.length = 1768 ∧
      (deployedInstance base stage slot).2.2 = ok (.Ok (JHg_World.e2.heap,()))
```

## Retained fixture premise

```lean
def FixturePdaRuntime (base : Ops) : Prop :=
  ∀ seeds program, Call seeds program → base.op38 seeds program=JHs_PDA.derive seeds program
```
