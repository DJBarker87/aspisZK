# Frozen consumer statements

Verbatim declarations from `lean/PV_EVH_FixtureConsumer.lean` at `5e9df8eb46b7ba32cde9b0eb430d93f5fc41fffd`. Names resolve in `namespace PV_EVH_FixtureConsumer` with the opens in the source. No binder or premise is suppressed.

## public_fibre

```lean
theorem public_fibre (handle : PV_RJ4IDB.Bytes) :
    ∃ w : R1Z.PV_RJDec_V047.H.Instance,
      R1Z.PV_RJDec_V047.H.public w = (deployedStatement handle).1
```

## two_transaction_nonvacuity

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

## instance_nonvacuity

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

`deployedInstance` is exactly the ordered triple of the two TX1 wrapper calls and the TX2 wrapper call displayed in the frozen source. `deployedStatement handle` is `R1Z.PV_RJ4IDB_CallerLive.callerStatement handle`.
