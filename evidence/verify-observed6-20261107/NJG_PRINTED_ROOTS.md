# Printed source/model root statements

Exact Lean output from NJG_L085; proof terms omitted here, retained in stdout.log. No native closure follows from a model dictionary parameter.

```lean
theorem AspisR1.NJG_FinishInstall.source : ∀ {H : Type} (R : AspisR1PublicPreparation.RoundModel.Boundaries)
  (F : AspisR1PublicPreparation.FinishModel.Boundaries) (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
  (pubdata : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (pre : AspisR1PublicPreparation.r1_wire.Prefix) (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
  (challenges : AspisR1PublicPreparation.r1_wire.Challenges),
  AspisR1.NJG_FinishBody.r1_semantic.verify_finish (AspisR1.NJG_FinishInstall.install R F) D pubdata pre t challenges
      none =
    AspisR1PublicPreparation.FinishModel.finish R (AspisR1.NJG_FinishInstall.model F) D pubdata pre t challenges none
```

```lean
theorem AspisR1.NJG_ObservedInstall.source : ∀ {H : Type} (R : AspisR1PublicPreparation.RoundModel.Boundaries)
  (F : AspisR1PublicPreparation.FinishModel.Boundaries) (D : NIX_EmittedTypes.aspis_core.digest.Digest32 H)
  (pubdata : NIX_EmittedTypes.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (hash : H),
  AspisR1.NJG_Results.upResult
      (AspisR1.NIX_ObservedBody.emitted (AspisR1.NJG_ObservedInstall.install R F) D pubdata bytes hash none) =
    AspisR1PublicPreparation.VerifyPrefix.verify
      (fun {H} => AspisR1PublicPreparation.FinishModel.finish R (AspisR1.NJG_FinishInstall.model F))
      (AspisR1.NJG_InputCarriers.upDigest D) (AspisR1.NJG_InputCarriers.upPublic pubdata) bytes hash none
```

```lean
theorem AspisR1.NJG_CurrentEquation.source : ∀ (R : AspisR1PublicPreparation.RoundModel.Boundaries)
  (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : AspisR1.ClaimsUnrolledFinish.StdCalls) {H : Type}
  (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
  (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (hash : H),
  AspisR1.NJG_CurrentEquation.verify R (AspisR1.ClaimsUnrolledFinish.install std (AspisR1.FIp_Install.boundaries seed))
      D pubdata bytes hash =
    AspisR1CurrentCaller.S1SemanticInstallation.verify R
      (AspisR1.ClaimsUnrolledFinish.install std (AspisR1.FIp_Install.boundaries seed)) D pubdata bytes hash
```

```lean
theorem AspisR1.NJG_CurrentEquation.slot : ∀ (base : AspisR1CurrentCaller.Ops)
  (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : AspisR1.ClaimsUnrolledFinish.StdCalls) {H : Type}
  (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
  (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (hash : H),
  (AspisR1.NJG_CurrentEquation.ops base seed std).op9 D pubdata bytes hash none =
    (AspisR1.RowShape_InstalledSlots.verifierOps (AspisR1.NJG_CurrentEquation.ops base seed std)
          (AspisR1.FIp_Install.boundaries seed) std).op9
      D pubdata bytes hash none
```

```lean
theorem AspisR1.NJG_CallerInstall.prepare : ∀ (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
  (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : AspisR1.ClaimsUnrolledFinish.StdCalls) {H : Type}
  (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
  (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (proof : Aeneas.Std.Slice Aeneas.Std.U8) (hash : H) (g : AspisR1.NHL_PrepareStages.Scratch),
  AspisR1.NHL_EmittedPrepare.prepare
      (AspisR1.NHL_Packets.installed
        (AspisR1.NHW_Prepare.nativeChildren (AspisR1.NJG_CurrentEquation.ops base seed std)) reserved)
      D pubdata proof hash none g =
    AspisR1CurrentCaller.verifier.candidate.prepare
      (AspisR1.NHL_PrepareModel.children
        (AspisR1.NHL_Packets.installed
          (AspisR1.NHW_Prepare.nativeChildren (AspisR1.NJG_CurrentEquation.ops base seed std)) reserved)
        (AspisR1.RowShape_InstalledSlots.verifierOps (AspisR1.NJG_CurrentEquation.ops base seed std)
          (AspisR1.FIp_Install.boundaries seed) std))
      D pubdata proof hash none g
```

```lean
theorem AspisR1.NJG_CallerInstall.tx1 : ∀ (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
  (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : AspisR1.ClaimsUnrolledFinish.StdCalls) {H : Type}
  (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
  (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (publicBytes proof : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.Usize) (hash : H),
  AspisR1.NHW_EmittedTx1.tx1
      (AspisR1.NHL_Packets.installed
        (AspisR1.NHW_DriverInstantiation.packetOps (AspisR1.NJG_CurrentEquation.ops base seed std)
          (AspisR1.RowShape_InstalledSlots.verifierOps (AspisR1.NJG_CurrentEquation.ops base seed std)
            (AspisR1.FIp_Install.boundaries seed) std))
        reserved)
      (AspisR1.NHW_EmittedPrepare.prepare
        (AspisR1.NHL_Packets.installed
          (AspisR1.NHW_DriverInstantiation.packetOps (AspisR1.NJG_CurrentEquation.ops base seed std)
            (AspisR1.RowShape_InstalledSlots.verifierOps (AspisR1.NJG_CurrentEquation.ops base seed std)
              (AspisR1.FIp_Install.boundaries seed) std))
          reserved))
      D pubdata publicBytes proof k hash none =
    AspisR1CurrentCaller.verifier.candidate.tx1
      (AspisR1.NHL_DriverModel.txOps
        (AspisR1.NHW_DriverInstantiation.packetOps (AspisR1.NJG_CurrentEquation.ops base seed std)
          (AspisR1.RowShape_InstalledSlots.verifierOps (AspisR1.NJG_CurrentEquation.ops base seed std)
            (AspisR1.FIp_Install.boundaries seed) std))
        (AspisR1.RowShape_InstalledSlots.verifierOps (AspisR1.NJG_CurrentEquation.ops base seed std)
          (AspisR1.FIp_Install.boundaries seed) std)
        reserved)
      D pubdata publicBytes proof k hash none
```
