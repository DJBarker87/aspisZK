# Exact kernel-loaded plan and headline statements

Partial diagnostic environment (NII_DIAGNOSTIC_IMPORT); full all-slices owner conflict remains. These statements supply none of their physical/native hypotheses.

## AspisR1.RPx_Deployed.deployed

```lean
@AspisR1.RPx_Deployed.deployed : ∀ {W A CoreError Tx : Type}
  (L : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record)),
  @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L →
    ∀
      (copy :
        AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
          Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record)),
      @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy →
        ∀ (allocator : AspisR1.S2W_D189Wrappers.Allocator A) (e1 e2 : AspisR1.S2W_D189Entry.Entry) (w1 w2 : W),
          @AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission W L e1 w1
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            @AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission W L e2 w2
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
              ∀ (missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
                (reservation : AspisR1.NP6_StdModel.Reservation) (native1 : AspisR1.S2W_ExtractionBoundary.First)
                (native2 : AspisR1.S2W_ExtractionBoundary.Second)
                (hashv : AspisR1.S2Z.Oracle.Parts → Aeneas.Std.Result.{0} AspisR1.S2Z.Oracle.Digest),
                AspisR1.S2W_DigestExtraction.AeneasExtraction
                    (@AspisR1.DrvC_Installation.sdk AspisR1.FIo_Install.W CoreError
                      (@AspisR1.FIp_Install.configuration CoreError indexError
                        (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing indexError reservation)
                        reservation))
                    native1 native2 hashv →
                  ∀ (sha256 H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
                    AspisR1.S2W_ExtractionBoundary.P1 sha256 H →
                      AspisR1.S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 →
                        ∀ (data1 data2 : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                          (slot : AspisR1.S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
                          (saved : Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                          (post1 post2 : AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)),
                          @Eq.{1}
                              (Aeneas.Std.Result.{0}
                                (Aeneas.Std.core.result.Result.{0, 0}
                                  (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                                  AspisR1.AdapterRw.Cuts.PE))
                              (@AspisR1.S2W_D189Wrappers.first A native1 copy allocator e1 AspisR1.CPH_Program.verifier
                                data1 state1)
                              (@Aeneas.Std.Result.ok.{0}
                                (Aeneas.Std.core.result.Result.{0, 0}
                                  (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                                  AspisR1.AdapterRw.Cuts.PE)
                                (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                  (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                                  AspisR1.AdapterRw.Cuts.PE
                                  (@Prod.mk.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A) saved
                                    (@Prod.mk.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A post1
                                      final1)))) →
                            @Eq.{1}
                                (Aeneas.Std.Result.{0}
                                  (Aeneas.Std.core.result.Result.{0, 0}
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A)
                                    AspisR1.AdapterRw.Cuts.PE))
                                (@AspisR1.S2W_D189Wrappers.second A native2 allocator e2 AspisR1.CPH_Program.verifier
                                  data2 slot state2)
                                (@Aeneas.Std.Result.ok.{0}
                                  (Aeneas.Std.core.result.Result.{0, 0}
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A)
                                    AspisR1.AdapterRw.Cuts.PE)
                                  (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A)
                                    AspisR1.AdapterRw.Cuts.PE
                                    (@Prod.mk.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A post2
                                      final2))) →
                              ∀
                                (root :
                                  Aeneas.Std.Array.{0} Aeneas.Std.U8
                                    (Aeneas.Std.Usize.ofNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) ⋯))
                                (length : Aeneas.Std.U32)
                                (prior :
                                  AspisV8R19.MemoizedProgramLaw.Program AspisV8R19.DuplexFrames.Bytes
                                    AspisV8R19.SourceDuplexStep.State Unit)
                                (words : AspisR1.CanonicalCutEnrichedTranscript.Words)
                                (p : AspisR1.CPG_Projection.Observations Tx A) (t u : Tx)
                                (actions : List.{0} (AspisR1.CPP_BankState.Action A)),
                                @AspisR1.CPH_Game.DeployedPairExecution Tx A p t u e1 e2 saved actions native1 native2
                                    copy allocator AspisR1.CPH_Program.verifier →
                                  @AspisR1.CPR_DataPersistence.TwoTransactionLaw Tx Nat
                                      (@AspisR1.CPG_Projection.adjacent Tx A p)
                                      (@AspisR1.CPG_Projection.ordinary Tx A p
                                        (AspisR1.Hist_Nonvacuity.key
                                          (Aeneas.Std.U8.ofNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯)))
                                      (@AspisR1.CPG_Projection.before Tx A p) (@AspisR1.CPG_Projection.tentative Tx A p)
                                      (@AspisR1.CPG_Projection.success Tx A p) (@AspisR1.CPG_Projection.loaded Tx A p) →
                                    ∀ (D : AspisR1.LiteralByteProtocol.Decoder) (a : AspisR1.SCE_Experiment.Adversary A)
                                      (Q0 Q1 : Nat),
                                      (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
                                          @LE.le.{0} Nat instLENat
                                            (@List.length.{0}
                                              (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                AspisV8R19.SourceDuplexStep.State)
                                              (@AspisR1.ARW_Induced.issued A native1 copy allocator
                                                AspisR1.CPH_Program.verifier a H))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q0 Q1)) →
                                        have P :=
                                          @AspisR1.ARW_Induced.program A native1 copy allocator
                                            AspisR1.CPH_Program.verifier a;
                                        have runtime :=
                                          @AspisR1.ARX_AdmittedRuntime.runtime W A CoreError Tx L copy allocator
                                            (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing indexError
                                              reservation)
                                            indexError reservation native1 native2 hashv a;
                                        have select := fun x =>
                                          AspisR1.P2P_NativeSelection.pair
                                            (@AspisR1.DrvC_Installation.sdk AspisR1.FIo_Install.W CoreError
                                              (@AspisR1.FIp_Install.configuration CoreError indexError
                                                (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                  indexError reservation)
                                                reservation))
                                            AspisR1.CPH_Program.verifier e1 e2 data2 slot;
                                        And
                                          (@AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary Unit
                                            (AspisR1.P6C_Extension.dictionary hashv H) Unit.unit H
                                            AspisR1.Op5T_P6.parent AspisR1.Op5T_P6.parent AspisR1.Op5T_P6.parent
                                            AspisR1.MultiproofConeP6Batch.referenceLeaf)
                                          (And
                                            (@Eq.{1} AspisR1.OraclePortRuntimeBindingC7.Verifier
                                              (@AspisR1.DrvC_Implementation.driver AspisR1.FIo_Install.W CoreError
                                                (@AspisR1.FIp_Install.configuration CoreError indexError
                                                  (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                    indexError reservation)
                                                  reservation))
                                              (@AspisR1.DrvC_SourceEntry.source AspisR1.FIo_Install.W CoreError
                                                (@AspisR1.FIp_Install.configuration CoreError indexError
                                                  (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                    indexError reservation)
                                                  reservation)
                                                hashv))
                                            (And
                                              (@Eq.{2} AdapterRw.Ops
                                                (@AspisR1.DrvC_Installation.sdk AspisR1.FIo_Install.W CoreError
                                                  (@AspisR1.FIp_Install.configuration CoreError indexError
                                                    (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                      indexError reservation)
                                                    reservation))
                                                (@AspisR1.SdkD_PairBatches.dictionary AspisR1.FIo_Install.W CoreError
                                                  (@AspisR1.DrvC_Installation.Configuration.adapter
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.currentBase
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.stageBase
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.finish AspisR1.FIo_Install.W
                                                    CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.reserved
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W
                                                    CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.geometry
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.boundaries
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.std AspisR1.FIo_Install.W
                                                    CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))))
                                              (And
                                                (@AspisR1.FJv_DResult.Outcome W AspisR1.FIo_Install.W CoreError L e1 e2
                                                  w1 w2
                                                  (@AspisR1.DrvC_Installation.Configuration.adapter
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.currentBase
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.reserved
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W
                                                    CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.geometry
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.stageBase
                                                    AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (@AspisR1.DrvC_Installation.Configuration.finish AspisR1.FIo_Install.W
                                                    CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  (AspisR1.FIp_Install.boundaries
                                                    (@AspisR1.DrvC_Installation.Configuration.boundaries
                                                      AspisR1.FIo_Install.W CoreError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)))
                                                  reservation AspisR1.CPH_Program.verifier data1 data2 slot saved post1
                                                  post2 H
                                                  (@AspisR1.DrvC_Implementation.driver AspisR1.FIo_Install.W CoreError
                                                    (@AspisR1.FIp_Install.configuration CoreError indexError
                                                      (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                        indexError reservation)
                                                      reservation))
                                                  prior (@AspisR1.CPG_Projection.Observations.physicalEvents Tx A p t)
                                                  hashv
                                                  (@AspisR1.BinRawByteCollisionTargets.event
                                                    (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes
                                                      AspisV8R19.SourceDuplexStep.State AspisR1.F3X_Projection.Output)
                                                    (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message
                                                      AspisWideTower.WideExact AspisR1.SelectedTranscriptParams.L
                                                      AspisR1.SelectedTranscriptParams.params)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        Q0 Q1)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2965)
                                                        (instOfNatNat (nat_lit 2965))))
                                                    (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                                                      AspisV8R19.SourceDuplexStep.State
                                                      (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes
                                                        AspisV8R19.SourceDuplexStep.State AspisR1.F3X_Projection.Output)
                                                      H
                                                      (@AspisR1.Hiq_RecordedJoint.program AspisR1.F3X_Projection.Output
                                                        (@AspisR1.F3X_Account.program AspisR1.FIo_Install.W CoreError
                                                          (@AspisR1.FIp_Install.configuration CoreError indexError
                                                            (@AspisR1.IDa_Deployed.deployedConfiguration CoreError
                                                              missing indexError reservation)
                                                            reservation)
                                                          hashv P)
                                                        AspisR1.F3X_Projection.project select))))
                                                (And
                                                  (And
                                                    (@AspisR1.F3X_ModelClaims.Claims AspisR1.FIo_Install.W CoreError
                                                      (@AspisR1.FIp_Install.configuration CoreError indexError
                                                        (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                          indexError reservation)
                                                        reservation)
                                                      D P
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        Q0 Q1))
                                                    (And
                                                      (@AspisR1.F3Y_SourceClaims.Claims AspisR1.FIo_Install.W CoreError
                                                        (@AspisR1.FIp_Install.configuration CoreError indexError
                                                          (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                            indexError reservation)
                                                          reservation)
                                                        D hashv P
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          Q0 Q1)
                                                        select)
                                                      (And
                                                        (@AspisR1.F3Y_AccountMass.Claims AspisR1.FIo_Install.W CoreError
                                                          (@AspisR1.FIp_Install.configuration CoreError indexError
                                                            (@AspisR1.IDa_Deployed.deployedConfiguration CoreError
                                                              missing indexError reservation)
                                                            reservation)
                                                          hashv P
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) Q0 Q1)
                                                          select)
                                                        ⋯)))
                                                  (And
                                                    (And
                                                      (@Eq.{1}
                                                        (Aeneas.Std.Result.{0}
                                                          (Aeneas.Std.core.result.Result.{0, 0}
                                                            (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                                            AspisR1.AdapterRw.Cuts.PE))
                                                        (native1 AspisR1.CPH_Program.verifier e1.first data1)
                                                        (@Aeneas.Std.Result.ok.{0}
                                                          (Aeneas.Std.core.result.Result.{0, 0}
                                                            (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                                            AspisR1.AdapterRw.Cuts.PE)
                                                          (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                                            (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                                            AspisR1.AdapterRw.Cuts.PE saved)))
                                                      (And
                                                        (@Eq.{1} Nat
                                                          (@List.length.{0} Aeneas.Std.U8
                                                            (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                              (fun l =>
                                                                @LE.le.{0} Nat instLENat
                                                                  (@List.length.{0} Aeneas.Std.U8 l)
                                                                  Aeneas.Std.Usize.max)
                                                              saved))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1768)
                                                            (instOfNatNat (nat_lit 1768))))
                                                        ⋯))
                                                    (And
                                                      (@AspisR1.Rc2_Events.Facts A AspisR1.FIo_Install.W CoreError
                                                        (@AspisR1.FIp_Install.configuration CoreError indexError
                                                          (@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing
                                                            indexError reservation)
                                                          reservation)
                                                        hashv native1 native2 copy allocator
                                                        AspisR1.CPH_Program.verifier H saved)
                                                      (And
                                                        (@AspisR1.CPH_Protection.Facts Tx A p t saved
                                                          AspisR1.CPH_Program.verifier)
                                                        ⋯)))))))
'AspisR1.RPx_Deployed.deployed' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGR_HISTORY.saved_to_loaded

```lean
AspisR1.NGR_HISTORY.saved_to_loaded : ∀ (prepared : AspisR1.CheckpointBytes5Writer.Prepared)
  (accumulator : AspisR1.CheckpointBytes5Writer.Accumulator)
  (domain : AspisR1.NGC_KNE_Caller.WriterDomain prepared accumulator) (hp hu hc : AspisR1.CheckpointBytes5Effect.Digest)
  {Tx A W : Type} (p : AspisR1.CPG_Projection.Observations Tx A) (t u : Tx) (e1 e2 : AspisR1.S2W_D189Entry.Entry)
  (actions : List.{0} (AspisR1.CPP_BankState.Action A)) (n1 : AspisR1.S2W_ExtractionBoundary.First)
  (n2 : AspisR1.S2W_ExtractionBoundary.Second)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record)),
  @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy →
    ∀ (allocator : AspisR1.S2W_D189Wrappers.Allocator A),
      @AspisR1.S2Trust.Valid (Nat → AspisR1.S2W_D189Entry.Record) e1.heap →
        ∀ (id system : AspisR1.S2W_ExtractionBoundary.Program) (data1 : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
          (state1 final1 : A) (post1 : AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)),
          @AspisR1.CPH_Game.DeployedPairExecution Tx A p t u e1 e2
              (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) actions n1 n2 copy allocator id →
            @Eq.{1}
                (Aeneas.Std.Result.{0}
                  (Aeneas.Std.core.result.Result.{0, 0}
                    (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                      (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                    AspisR1.AdapterRw.Cuts.PE))
                (@AspisR1.S2W_D189Wrappers.first A n1 copy allocator e1 id data1 state1)
                (@Aeneas.Std.Result.ok.{0}
                  (Aeneas.Std.core.result.Result.{0, 0}
                    (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                      (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                    AspisR1.AdapterRw.Cuts.PE)
                  (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                    (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                      (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                    AspisR1.AdapterRw.Cuts.PE
                    (@Prod.mk.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                      (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A)
                      (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)
                      (@Prod.mk.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A post1 final1)))) →
              @AspisR1.CPH_Protection.Facts Tx A p t
                  (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) id →
                @AspisR1.CPG_Projection.ordinary Tx A p system t
                    (@Prod.fst.{0, 0} Nat Nat
                      ((@AspisR1.CPG_Projection.Observations.layout Tx A p t).handles
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @AspisR1.CPR_DataPersistence.TwoTransactionLaw Tx Nat (@AspisR1.CPG_Projection.adjacent Tx A p)
                      (@AspisR1.CPG_Projection.ordinary Tx A p system) (@AspisR1.CPG_Projection.before Tx A p)
                      (@AspisR1.CPG_Projection.tentative Tx A p) (@AspisR1.CPG_Projection.success Tx A p)
                      (@AspisR1.CPG_Projection.loaded Tx A p) →
                    ∀ (L : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record)),
                      @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L →
                        ∀ (w2 : W),
                          @AspisR1.S2Trust.Library.related W (Nat → AspisR1.S2W_D189Entry.Record) L w2 e2.heap →
                            @AspisR1.S2Trust.Valid (Nat → AspisR1.S2W_D189Entry.Record) e2.heap →
                              And (@AspisR1.CPG_Projection.adjacent Tx A p t u)
                                (And
                                  (@Eq.{1} Nat
                                    (@Prod.fst.{0, 0} Nat Nat
                                      ((@AspisR1.CPG_Projection.Observations.layout Tx A p t).handles
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    (@Prod.fst.{0, 0} Nat Nat
                                      ((@AspisR1.CPG_Projection.Observations.layout Tx A p u).handles
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                                  (And (@Eq.{1} Bool (@AspisR1.CPG_Projection.success Tx A p t) Bool.true)
                                    (And
                                      (@Eq.{1} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                        (@AspisR1.CPG_Projection.Observations.copied Tx A p t)
                                        (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc))
                                      (And
                                        (@Eq.{1} Nat
                                          (@List.length.{0} Aeneas.Std.U8
                                            (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                              (fun l =>
                                                @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                  Aeneas.Std.Usize.max)
                                              (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1768) (instOfNatNat (nat_lit 1768))))
                                        (And
                                          (@Eq.{1} (Option.{0} AspisV8R19.DuplexFrames.Bytes)
                                            (@AspisR1.CPG_Projection.loaded Tx A p u
                                              (@Prod.fst.{0, 0} Nat Nat
                                                ((@AspisR1.CPG_Projection.Observations.layout Tx A p t).handles
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                            (@Option.some.{0} AspisV8R19.DuplexFrames.Bytes
                                              (AspisR1.MultiproofConeCanonical.bytesOf
                                                (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                  (fun l =>
                                                    @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                      Aeneas.Std.Usize.max)
                                                  (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu
                                                    hc)))))
                                          (And
                                            (@Eq.{1} (List.{0} Aeneas.Std.U8)
                                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                    Aeneas.Std.Usize.max)
                                                (e2.buffers
                                                  (@Prod.fst.{0, 0} Nat Nat
                                                    (e2.handles
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                    Aeneas.Std.Usize.max)
                                                (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)))
                                            (And
                                              (@Eq.{1} AspisV8R19.DuplexFrames.Bytes
                                                (AspisR1.S2W_EntryWriteHistory.payloadBytes
                                                  AspisR1.S2W_ReturnedCheckpoint.encode
                                                  (@AspisR1.S2Trust.Heap.payload (Nat → AspisR1.S2W_D189Entry.Record)
                                                    post1
                                                    (@Prod.fst.{0, 0} Nat Nat
                                                      (@AspisR1.S2Trust.Heap.accounts
                                                        (Nat → AspisR1.S2W_D189Entry.Record) e1.heap
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1768) (instOfNatNat (nat_lit 1768))))
                                                (AspisR1.MultiproofConeCanonical.bytesOf
                                                  (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                    (fun l =>
                                                      @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                        Aeneas.Std.Usize.max)
                                                    (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu
                                                      hc))))
                                              (And
                                                (@Eq.{1} AspisV8R19.DuplexFrames.Bytes
                                                  (AspisR1.S2W_EntryWriteHistory.payloadBytes
                                                    AspisR1.S2W_ReturnedCheckpoint.encode
                                                    (@AspisR1.S2Trust.Library.cellPayload W
                                                      (Nat → AspisR1.S2W_D189Entry.Record) L w2
                                                      (@AspisR1.S2Trust.Library.accountData W
                                                        (Nat → AspisR1.S2W_D189Entry.Record) L w2
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                                    (@AspisR1.S2Trust.Library.cellPayload W
                                                          (Nat → AspisR1.S2W_D189Entry.Record) L w2
                                                          (@AspisR1.S2Trust.Library.accountData W
                                                            (Nat → AspisR1.S2W_D189Entry.Record) L w2
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                              (instOfNatNat (nat_lit 6))))).descriptor.length)
                                                  (AspisR1.MultiproofConeCanonical.bytesOf
                                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                      (fun l =>
                                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                          Aeneas.Std.Usize.max)
                                                      (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu
                                                        hc))))
                                                (@AspisR1.CPH_Trace.Facts Tx A p t u
                                                  (AspisR1.NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)
                                                  n1 n2 copy allocator id)))))))))
'AspisR1.NGR_HISTORY.saved_to_loaded' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGS_CARRIERS.same_inputs_or_collision

```lean
@AspisR1.NGS_CARRIERS.same_inputs_or_collision : ∀ {A C : Type}
  (base : AspisR1.DrvC_Installation.Configuration AspisR1.FIo_Install.W C) (err : C)
  (r : AspisR1.NP6_StdModel.Reservation)
  (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result.{0} AspisR1.SdkC_Source.Digest)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (allocator : AspisR1.S2W_D189Wrappers.Allocator A) (a : AspisR1.SCE_Experiment.Adversary A)
  (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (Q : Nat),
  @LE.le.{0} Nat instLENat
      (@AspisR1.ART_AdversaryWork.work A AspisR1.FIo_Install.W C (@AspisR1.FIp_Install.configuration C err base r) hashv
        copy allocator AspisR1.CPH_Program.verifier a H)
      Q →
    ∀
      (reached :
        @Eq.{1} Bool
          (@Option.isSome.{0}
            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A) (AspisR1.GExq_AccountExperiment.SecondReply A))
            (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
              (Option.{0}
                (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                  (AspisR1.GExq_AccountExperiment.SecondReply A)))
              (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                  (Option.{0}
                    (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                      (AspisR1.GExq_AccountExperiment.SecondReply A))))
                (@Prod.snd.{0, 0}
                  (List.{0} (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State))
                  (AspisR1.GExq_AccountExperiment.Outcome A)
                  (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                    (AspisR1.GExq_AccountExperiment.Outcome A) H
                    (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                      (@AspisR1.FIp_Install.configuration C err base r) hashv copy allocator
                      AspisR1.CPH_Program.verifier a))))))
          Bool.true)
      (f : AspisR1.S2W_NativeConsolidation.FirstCut) (s : AspisR1.S2W_NativeConsolidation.SecondCut)
      (finish1 : Aeneas.Std.Usize),
      @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.AdapterRw.Cuts.Account)
          (@Aeneas.Std.Slice.index_usize.{0} AspisR1.AdapterRw.Cuts.Account
            (@AspisR1.GExq_AccountExperiment.FirstInputs.entry A
                (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                  (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                    (Option.{0}
                      (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                        (AspisR1.GExq_AccountExperiment.SecondReply A))))
                  (@Prod.snd.{0, 0}
                    (List.{0} (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State))
                    (AspisR1.GExq_AccountExperiment.Outcome A)
                    (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                      (AspisR1.GExq_AccountExperiment.Outcome A) H
                      (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                        (@AspisR1.FIp_Install.configuration C err base r) hashv copy allocator
                        AspisR1.CPH_Program.verifier a))))).first
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯))
          (@Aeneas.Std.Result.ok.{0} AspisR1.AdapterRw.Cuts.Account f.proofAccount) →
        @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.AdapterRw.Cuts.Account)
            (@Aeneas.Std.Slice.index_usize.{0} AspisR1.AdapterRw.Cuts.Account
              (@AspisR1.GExq_AccountExperiment.FirstInputs.entry A
                  (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                    (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                      (Option.{0}
                        (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                          (AspisR1.GExq_AccountExperiment.SecondReply A))))
                    (@Prod.snd.{0, 0}
                      (List.{0} (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State))
                      (AspisR1.GExq_AccountExperiment.Outcome A)
                      (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                        AspisV8R19.SourceDuplexStep.State (AspisR1.GExq_AccountExperiment.Outcome A) H
                        (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                          (@AspisR1.FIp_Install.configuration C err base r) hashv copy allocator
                          AspisR1.CPH_Program.verifier a))))).first
              (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) ⋯))
            (@Aeneas.Std.Result.ok.{0} AspisR1.AdapterRw.Cuts.Account f.publicAccount) →
          @Eq.{1}
              (Aeneas.Std.Result.{0}
                (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                  AdapterRw.solana_program_error.ProgramError))
              (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
                (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                  (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                f.proofAccount)
              (@Aeneas.Std.Result.ok.{0}
                (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                  AdapterRw.solana_program_error.ProgramError)
                (@Aeneas.Std.core.result.Result.Ok.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                  AdapterRw.solana_program_error.ProgramError f.raw)) →
            @Eq.{1}
                (Aeneas.Std.Result.{0}
                  (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                    AdapterRw.solana_program_error.ProgramError))
                (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
                  (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                    (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                  f.publicAccount)
                (@Aeneas.Std.Result.ok.{0}
                  (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                    AdapterRw.solana_program_error.ProgramError)
                  (@Aeneas.Std.core.result.Result.Ok.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                    AdapterRw.solana_program_error.ProgramError f.pub)) →
              @Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8))
                  (@Aeneas.Std.core.slice.index.Slice.index Aeneas.Std.U8
                    (Aeneas.Std.core.ops.range.Range.{0} Aeneas.Std.Usize) (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                    (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice Aeneas.Std.U8) f.raw
                    (@Aeneas.Std.core.ops.range.Range.mk.{0} Aeneas.Std.Usize
                      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 688) (instOfNatNat (nat_lit 688))) ⋯)
                      finish1))
                  (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8) f.proof) →
                @Eq.{1} Nat
                    (@List.length.{0} Aeneas.Std.U8
                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                        (fun l => @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l) Aeneas.Std.Usize.max)
                        f.raw))
                    (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize finish1) →
                  @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.AdapterRw.Cuts.Account)
                      (@Aeneas.Std.Slice.index_usize.{0} AspisR1.AdapterRw.Cuts.Account
                        ((@AspisR1.GExq_AccountExperiment.SecondInputs.entry A
                              (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                (AspisR1.GExq_AccountExperiment.SecondReply A)
                                (@Option.get.{0}
                                  (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                    (AspisR1.GExq_AccountExperiment.SecondReply A))
                                  (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                    (Option.{0}
                                      (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                        (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                    (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                      (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                        (Option.{0}
                                          (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                            (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                      (@Prod.snd.{0, 0}
                                        (List.{0}
                                          (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State))
                                        (AspisR1.GExq_AccountExperiment.Outcome A)
                                        (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                                          AspisV8R19.SourceDuplexStep.State (AspisR1.GExq_AccountExperiment.Outcome A) H
                                          (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                                            (@AspisR1.FIp_Install.configuration C err base r) hashv copy allocator
                                            AspisR1.CPH_Program.verifier a)))))
                                  reached))).second
                          AspisR1.S2W_D189Wrappers.secondSizes)
                        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯))
                      (@Aeneas.Std.Result.ok.{0} AspisR1.AdapterRw.Cuts.Account s.proofAccount) →
                    @Eq.{1}
                        (Aeneas.Std.Result.{0}
                          (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                            AdapterRw.solana_program_error.ProgramError))
                        (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
                          (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                            (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                          s.proofAccount)
                        (@Aeneas.Std.Result.ok.{0}
                          (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                            AdapterRw.solana_program_error.ProgramError)
                          (@Aeneas.Std.core.result.Result.Ok.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                            AdapterRw.solana_program_error.ProgramError s.raw)) →
                      @Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8))
                          (@Aeneas.Std.core.slice.index.Slice.index Aeneas.Std.U8
                            (Aeneas.Std.core.ops.range.Range.{0} Aeneas.Std.Usize) (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                            (Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice Aeneas.Std.U8) s.raw
                            (@Aeneas.Std.core.ops.range.Range.mk.{0} Aeneas.Std.Usize
                              (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 688) (instOfNatNat (nat_lit 688)))
                                ⋯)
                              s.finish))
                          (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8) s.proof) →
                        @Eq.{1} Nat
                            (@List.length.{0} Aeneas.Std.U8
                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l) Aeneas.Std.Usize.max)
                                s.raw))
                            (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize s.finish) →
                          ∀ (v : AdapterRw.r1_pool_adapter.ValidatedAsqa),
                            @Eq.{1}
                                (Aeneas.Std.Result.{0}
                                  (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ValidatedAsqa
                                    AdapterRw.solana_program_error.ProgramError))
                                (AdapterRw.r1_pool_adapter.owned.validate_asq8
                                  (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                                    (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                                  AspisR1.CPH_Program.verifier
                                  ((@AspisR1.GExq_AccountExperiment.SecondInputs.entry A
                                        (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                          (AspisR1.GExq_AccountExperiment.SecondReply A)
                                          (@Option.get.{0}
                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                              (AspisR1.GExq_AccountExperiment.SecondReply A))
                                            (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                              (Option.{0}
                                                (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                  (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                              (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                                (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                  (Option.{0}
                                                    (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                      (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                                (@Prod.snd.{0, 0}
                                                  (List.{0}
                                                    (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                      AspisV8R19.SourceDuplexStep.State))
                                                  (AspisR1.GExq_AccountExperiment.Outcome A)
                                                  (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                                                    AspisV8R19.SourceDuplexStep.State
                                                    (AspisR1.GExq_AccountExperiment.Outcome A) H
                                                    (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                                                      (@AspisR1.FIp_Install.configuration C err base r) hashv copy
                                                      allocator AspisR1.CPH_Program.verifier a)))))
                                            reached))).second
                                    AspisR1.S2W_D189Wrappers.secondSizes)
                                  (@AspisR1.GExq_AccountExperiment.SecondInputs.data A
                                    (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                      (AspisR1.GExq_AccountExperiment.SecondReply A)
                                      (@Option.get.{0}
                                        (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                          (AspisR1.GExq_AccountExperiment.SecondReply A))
                                        (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                          (Option.{0}
                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                              (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                          (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                              (Option.{0}
                                                (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                  (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                            (@Prod.snd.{0, 0}
                                              (List.{0}
                                                (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                  AspisV8R19.SourceDuplexStep.State))
                                              (AspisR1.GExq_AccountExperiment.Outcome A)
                                              (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                                                AspisV8R19.SourceDuplexStep.State
                                                (AspisR1.GExq_AccountExperiment.Outcome A) H
                                                (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                                                  (@AspisR1.FIp_Install.configuration C err base r) hashv copy allocator
                                                  AspisR1.CPH_Program.verifier a)))))
                                        reached)))
                                  (@AspisR1.GExq_AccountExperiment.SecondInputs.slot A
                                    (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                      (AspisR1.GExq_AccountExperiment.SecondReply A)
                                      (@Option.get.{0}
                                        (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                          (AspisR1.GExq_AccountExperiment.SecondReply A))
                                        (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                          (Option.{0}
                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                              (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                          (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                              (Option.{0}
                                                (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                  (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                            (@Prod.snd.{0, 0}
                                              (List.{0}
                                                (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                  AspisV8R19.SourceDuplexStep.State))
                                              (AspisR1.GExq_AccountExperiment.Outcome A)
                                              (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                                                AspisV8R19.SourceDuplexStep.State
                                                (AspisR1.GExq_AccountExperiment.Outcome A) H
                                                (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                                                  (@AspisR1.FIp_Install.configuration C err base r) hashv copy allocator
                                                  AspisR1.CPH_Program.verifier a)))))
                                        reached))))
                                (@Aeneas.Std.Result.ok.{0}
                                  (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ValidatedAsqa
                                    AdapterRw.solana_program_error.ProgramError)
                                  (@Aeneas.Std.core.result.Result.Ok.{0, 0} AdapterRw.r1_pool_adapter.ValidatedAsqa
                                    AdapterRw.solana_program_error.ProgramError v)) →
                              @Eq.{1}
                                  (Aeneas.Std.Result.{0}
                                    (Aeneas.Std.core.result.Result.{0, 0}
                                      (Aeneas.Std.Array.{0} Aeneas.Std.U8
                                        (Aeneas.Std.Usize.ofNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1880) (instOfNatNat (nat_lit 1880))) ⋯))
                                      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
                                  ((@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                                        (@AspisR1.FIp_Install.configuration C err base r) hashv H).op22
                                    v.statement)
                                  (@Aeneas.Std.Result.ok.{0}
                                    (Aeneas.Std.core.result.Result.{0, 0}
                                      (Aeneas.Std.Array.{0} Aeneas.Std.U8
                                        (Aeneas.Std.Usize.ofNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1880) (instOfNatNat (nat_lit 1880))) ⋯))
                                      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                                    (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                      (Aeneas.Std.Array.{0} Aeneas.Std.U8
                                        (Aeneas.Std.Usize.ofNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1880) (instOfNatNat (nat_lit 1880))) ⋯))
                                      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
                                      s.encoded)) →
                                ∀ (saved : Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8),
                                  @Eq.{1}
                                      (Aeneas.Std.Result.{0}
                                        (Aeneas.Std.core.result.Result.{0, 0}
                                          (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                          AdapterRw.solana_program_error.ProgramError))
                                      (AdapterRw.first_decoded
                                        (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                                          (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                                        f.semantic f.pub f.proof f.split)
                                      (@Aeneas.Std.Result.ok.{0}
                                        (Aeneas.Std.core.result.Result.{0, 0}
                                          (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                          AdapterRw.solana_program_error.ProgramError)
                                        (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                          (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                                          AdapterRw.solana_program_error.ProgramError saved)) →
                                    @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.AdapterRw.Cuts.Account)
                                        (@Aeneas.Std.Slice.index_usize.{0} AspisR1.AdapterRw.Cuts.Account
                                          ((@AspisR1.GExq_AccountExperiment.SecondInputs.entry A
                                                (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                  (AspisR1.GExq_AccountExperiment.SecondReply A)
                                                  (@Option.get.{0}
                                                    (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                      (AspisR1.GExq_AccountExperiment.SecondReply A))
                                                    (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                      (Option.{0}
                                                        (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                          (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                                      (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                                        (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                          (Option.{0}
                                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                              (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                                        (@Prod.snd.{0, 0}
                                                          (List.{0}
                                                            (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                              AspisV8R19.SourceDuplexStep.State))
                                                          (AspisR1.GExq_AccountExperiment.Outcome A)
                                                          (@AspisV8R19.MemoizedProgramLaw.eval
                                                            AspisV8R19.DuplexFrames.Bytes
                                                            AspisV8R19.SourceDuplexStep.State
                                                            (AspisR1.GExq_AccountExperiment.Outcome A) H
                                                            (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W
                                                              C (@AspisR1.FIp_Install.configuration C err base r) hashv
                                                              copy allocator AspisR1.CPH_Program.verifier a)))))
                                                    reached))).second
                                            AspisR1.S2W_D189Wrappers.secondSizes)
                                          (Aeneas.Std.Usize.ofNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) ⋯))
                                        (@Aeneas.Std.Result.ok.{0} AspisR1.AdapterRw.Cuts.Account s.checkpointAccount) →
                                      @Eq.{1}
                                          (Aeneas.Std.Result.{0}
                                            (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                                              AdapterRw.solana_program_error.ProgramError))
                                          (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
                                            (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                                              (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                                            s.checkpointAccount)
                                          (@Aeneas.Std.Result.ok.{0}
                                            (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                                              AdapterRw.solana_program_error.ProgramError)
                                            (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                              (Aeneas.Std.Slice.{0} Aeneas.Std.U8)
                                              AdapterRw.solana_program_error.ProgramError s.checkpoint)) →
                                        @Eq.{1} (List.{0} Aeneas.Std.U8)
                                            (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                              (fun l =>
                                                @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                  Aeneas.Std.Usize.max)
                                              ((@AspisR1.GExq_AccountExperiment.SecondInputs.entry A
                                                    (@Prod.fst.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                      (AspisR1.GExq_AccountExperiment.SecondReply A)
                                                      (@Option.get.{0}
                                                        (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                          (AspisR1.GExq_AccountExperiment.SecondReply A))
                                                        (@Prod.snd.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                          (Option.{0}
                                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                              (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                                          (@Prod.snd.{0, 0}
                                                            (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                              (Option.{0}
                                                                (Prod.{0, 0}
                                                                  (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                                  (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                                            (@Prod.snd.{0, 0}
                                                              (List.{0}
                                                                (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                                  AspisV8R19.SourceDuplexStep.State))
                                                              (AspisR1.GExq_AccountExperiment.Outcome A)
                                                              (@AspisV8R19.MemoizedProgramLaw.eval
                                                                AspisV8R19.DuplexFrames.Bytes
                                                                AspisV8R19.SourceDuplexStep.State
                                                                (AspisR1.GExq_AccountExperiment.Outcome A) H
                                                                (@AspisR1.ART_PartialAccount.account A
                                                                  AspisR1.FIo_Install.W C
                                                                  (@AspisR1.FIp_Install.configuration C err base r)
                                                                  hashv copy allocator AspisR1.CPH_Program.verifier
                                                                  a)))))
                                                        reached))).buffers
                                                (@Prod.fst.{0, 0} Nat Nat
                                                  ((@AspisR1.GExq_AccountExperiment.SecondInputs.entry A
                                                        (@Prod.fst.{0, 0}
                                                          (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                          (AspisR1.GExq_AccountExperiment.SecondReply A)
                                                          (@Option.get.{0}
                                                            (Prod.{0, 0} (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                              (AspisR1.GExq_AccountExperiment.SecondReply A))
                                                            (@Prod.snd.{0, 0}
                                                              (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                              (Option.{0}
                                                                (Prod.{0, 0}
                                                                  (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                                  (AspisR1.GExq_AccountExperiment.SecondReply A)))
                                                              (@Prod.snd.{0, 0}
                                                                (AspisR1.GExq_AccountExperiment.FirstInputs A)
                                                                (Prod.{0, 0}
                                                                  (AspisR1.GExq_AccountExperiment.FirstReply A)
                                                                  (Option.{0}
                                                                    (Prod.{0, 0}
                                                                      (AspisR1.GExq_AccountExperiment.SecondInputs A)
                                                                      (AspisR1.GExq_AccountExperiment.SecondReply A))))
                                                                (@Prod.snd.{0, 0}
                                                                  (List.{0}
                                                                    (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes
                                                                      AspisV8R19.SourceDuplexStep.State))
                                                                  (AspisR1.GExq_AccountExperiment.Outcome A)
                                                                  (@AspisV8R19.MemoizedProgramLaw.eval
                                                                    AspisV8R19.DuplexFrames.Bytes
                                                                    AspisV8R19.SourceDuplexStep.State
                                                                    (AspisR1.GExq_AccountExperiment.Outcome A) H
                                                                    (@AspisR1.ART_PartialAccount.account A
                                                                      AspisR1.FIo_Install.W C
                                                                      (@AspisR1.FIp_Install.configuration C err base r)
                                                                      hashv copy allocator AspisR1.CPH_Program.verifier
                                                                      a)))))
                                                            reached))).handles
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                                            (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                              (fun l =>
                                                @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                  Aeneas.Std.Usize.max)
                                              saved) →
                                          @Eq.{1}
                                              (Aeneas.Std.Result.{0}
                                                (Aeneas.Std.core.result.Result.{0, 0} Unit
                                                  AdapterRw.aspis_r1_cost_probe.verifier.Error))
                                              (@AdapterRw.Ops.op11
                                                (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                                                  (@AspisR1.FIp_Install.configuration C err base r) hashv H)
                                                AdapterRw.SolanaDigest
                                                (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
                                                  (@AspisR1.SCH_IdealSdk.dictionary AspisR1.FIo_Install.W C
                                                    (@AspisR1.FIp_Install.configuration C err base r) hashv H))
                                                s.pub s.proof s.checkpoint Unit.unit
                                                (@Option.none.{0}
                                                  (AdapterRw.aspis_r1_cost_probe.verifier.Phase →
                                                    Aeneas.Std.Result.{0} Unit)))
                                              (@Aeneas.Std.Result.ok.{0}
                                                (Aeneas.Std.core.result.Result.{0, 0} Unit
                                                  AdapterRw.aspis_r1_cost_probe.verifier.Error)
                                                (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit
                                                  AdapterRw.aspis_r1_cost_probe.verifier.Error Unit.unit)) →
                                            Or
                                              (And
                                                (@Eq.{1} AspisV8R19.DuplexFrames.Bytes
                                                  (AspisR1.MultiproofConeCanonical.bytesOf
                                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                      (fun l =>
                                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                          Aeneas.Std.Usize.max)
                                                      s.proof))
                                                  (AspisR1.MultiproofConeCanonical.bytesOf
                                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                      (fun l =>
                                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                          Aeneas.Std.Usize.max)
                                                      f.proof)))
                                                (@Eq.{1} AspisV8R19.DuplexFrames.Bytes
                                                  (AspisR1.MultiproofConeCanonical.bytesOf
                                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                      (fun l =>
                                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                          Aeneas.Std.Usize.max)
                                                      s.pub))
                                                  (AspisR1.MultiproofConeCanonical.bytesOf
                                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                      (fun l =>
                                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 l)
                                                          Aeneas.Std.Usize.max)
                                                      f.pub))))
                                              (@AspisR1.BinRawByteCollisionTargets.event
                                                (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes
                                                  AspisV8R19.SourceDuplexStep.State
                                                  (AspisR1.GExq_AccountExperiment.Outcome A))
                                                (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message
                                                  AspisWideTower.WideExact AspisR1.SelectedTranscriptParams.L
                                                  AspisR1.SelectedTranscriptParams.params)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
                                                (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes
                                                  AspisV8R19.SourceDuplexStep.State
                                                  (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes
                                                    AspisV8R19.SourceDuplexStep.State
                                                    (AspisR1.GExq_AccountExperiment.Outcome A))
                                                  H
                                                  (@AspisR1.Hiq_RecordedJoint.program
                                                    (AspisR1.GExq_AccountExperiment.Outcome A)
                                                    (@AspisR1.ART_PartialAccount.account A AspisR1.FIo_Install.W C
                                                      (@AspisR1.FIp_Install.configuration C err base r) hashv copy
                                                      allocator AspisR1.CPH_Program.verifier a)
                                                    (@AspisR1.ARQ_Observer.project A)
                                                    (@AspisR1.ARQ_Observer.select A AspisR1.FIo_Install.W C
                                                      (@AspisR1.FIp_Install.configuration C err base r)
                                                      AspisR1.CPH_Program.verifier))))
'AspisR1.NGS_CARRIERS.same_inputs_or_collision' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGP_OracleTransport.prefix_of_native

```lean
@AspisR1.NGP_OracleTransport.prefix_of_native : ∀ {A : Type}
  (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result.{0} AspisR1.SdkC_Source.Digest)
  (sha256 H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (code : AspisR1.CheckpointBytes5Effect.Code A) (observed : AspisR1.NGP_L181.Observation A),
  @AspisR1.NGP_L181.NativeAssociation A hashv code observed →
    AspisR1.S2W_ExtractionBoundary.P1 sha256 H →
      AspisR1.S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 → @AspisR1.NGP_L181.Prefix_statement A H code observed
'AspisR1.NGP_OracleTransport.prefix_of_native' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGP_OracleTransport.exact_of_returns

```lean
@AspisR1.NGP_OracleTransport.exact_of_returns : ∀ {A : Type}
  (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result.{0} AspisR1.SdkC_Source.Digest)
  (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (code : AspisR1.CheckpointBytes5Effect.Code A)
  (observed : AspisR1.NGP_L181.Observation A),
  @AspisR1.NGP_L181.NativeAssociation A hashv code observed →
    AspisR1.ARR_ReturnCoverage.ReturnsOnly (@AspisR1.NGP_L181.Observation.attempted A observed) →
      AspisR1.ARS_QueryTransport.Agrees H (@AspisR1.NGP_L181.Observation.attempted A observed) →
        @AspisR1.NGP_L181.Exact_statement A H code observed
'AspisR1.NGP_OracleTransport.exact_of_returns' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGP_TRANSCRIPT.actual_queries

```lean
AspisR1.NGP_TRANSCRIPT.actual_queries : ∀
  (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result.{0} AspisR1.SdkC_Source.Digest)
  (self : AspisR1PublicPreparation.transcript.Transcript Unit) (row : Aeneas.Std.U8)
  (payload : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (observed : AspisR1.NGP_L181.Observation AspisR1.NGQ_Effects.Reply),
  AspisR1.NHK_Invocation.Domain row payload →
    AspisR1.NHK_Invocation.Cuts hashv self row payload observed →
      @AspisR1.NGP_L181.NativeAssociation AspisR1.NGQ_Effects.Reply hashv
        (AspisR1.NGQ_Effects.code AspisR1.NGQ_TRANSCRIPT.boundaries self row payload) observed
'AspisR1.NGP_TRANSCRIPT.actual_queries' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NHZ_DRIVER.events_from_cuts

```lean
@AspisR1.NHZ_DRIVER.events_from_cuts : ∀ {A : Type}
  (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result.{0} AspisR1.SdkC_Source.Digest)
  (tx1 cutCode : AspisR1.CheckpointBytes5Effect.Code A) (observed : AspisR1.NGP_L181.Observation A),
  @AspisR1.NHZ_DRIVER.Cuts hashv A cutCode (@AspisR1.NGP_L181.Observation.result A observed)
      (@AspisR1.NGP_L181.Observation.attempted A observed) →
    @Eq.{2} (AspisR1.CheckpointBytes5Effect.Code A) cutCode tx1 →
      @AspisR1.NGP_L181.NativeAssociation A hashv tx1 observed
'AspisR1.NHZ_DRIVER.events_from_cuts' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NHZ_EXPERIMENT.same_law

```lean
@AspisR1.NHZ_EXPERIMENT.same_law : ∀ {W A C Tx : Type}
  (L : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (allocator : AspisR1.S2W_D189Wrappers.Allocator A)
  (c : AspisR1.DrvC_Installation.Configuration AspisR1.FIo_Install.W C) (err : C) (r : AspisR1.NP6_StdModel.Reservation)
  (native1 : AspisR1.S2W_ExtractionBoundary.First) (native2 : AspisR1.S2W_ExtractionBoundary.Second)
  (hashv : AspisR1.SdkC_Source.Parts → Aeneas.Std.Result.{0} AspisR1.SdkC_Source.Digest)
  (a : AspisR1.SCE_Experiment.Adversary A),
  AspisR1.S2W_DigestExtraction.AeneasExtraction
      (@AspisR1.DrvC_Installation.sdk AspisR1.FIo_Install.W C (@AspisR1.FIp_Install.configuration C err c r)) native1
      native2 hashv →
    @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy →
      ∀ (D : AspisR1.LiteralByteProtocol.Decoder) (words : AspisR1.CanonicalCutEnrichedTranscript.Words),
        @AspisR1.FIp_GlobalOwners.Owners AspisR1.FIo_Install.W C (@AspisR1.FIp_Install.configuration C err c r)
            (@AspisR1.DrvC_Installation.Configuration.boundaries AspisR1.FIo_Install.W C
              (@AspisR1.Rc2_Install.configuration AspisR1.FIo_Install.W C
                (@AspisR1.Rc5_Install.seed AspisR1.FIo_Install.W C err (@AspisR1.FIp_Install.select C r c)) r)) →
          ∀ (Q0 Q1 : Nat),
            (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
                @LE.le.{0} Nat instLENat
                  (@List.length.{0} (Prod.{0, 0} AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State)
                    (@AspisR1.ARW_Induced.issued A native1 copy allocator AspisR1.CPH_Program.verifier a H))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q0 Q1)) →
              ∀ (physical : AspisR1.F3T_Runtime.Runtime),
                @AspisR1.NHZ_EXPERIMENT.Realizes W A C Tx L copy allocator c err r native1 native2 hashv a physical →
                  And
                    (@Eq.{1} Rat (AspisR1.F3T_Runtime.deployedFailure physical)
                      (AspisR1.F3T_Runtime.deployedFailure
                        (@AspisR1.ARX_AdmittedRuntime.runtime W A C Tx L copy allocator c err r native1 native2 hashv
                          a)))
                    (And
                      (@LE.le.{0} Rat Rat.instLE (AspisR1.F3T_Runtime.deployedFailure physical)
                        (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                          (@AspisV8R19.MemoizedProgramLaw.lazyMean AspisV8R19.DuplexFrames.Bytes
                            AspisV8R19.SourceDuplexStep.State
                            (Prod.{0, 0}
                              (Prod.{0, 0} AspisR1.LiteralTranscript.Public (Nat → AspisR1.LiteralTranscript.Message))
                              Bool)
                            (@Pi.instFintype.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                              (fun a => AspisV8R19.DuplexFrames.Byte)
                              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                              {
                                  len :=
                                    @OfNat.ofNat.{0} Nat (nat_lit 31)
                                      (instOfNatNat (nat_lit 31)) }.instFintypeToTypeOrderHomFinHAddNatLenOfNat
                              fun a =>
                              {
                                  len :=
                                    @OfNat.ofNat.{0} Nat (nat_lit 255)
                                      (instOfNatNat (nat_lit 255)) }.instFintypeToTypeOrderHomFinHAddNatLenOfNat)
                            (fun a b =>
                              @instDecidableEqList.{0} AspisV8R19.DuplexFrames.Byte
                                (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) a
                                b)
                            (AspisR1.F3T_Charged.projected D
                              (AspisR1.F3T_Canon.canon
                                (@AspisR1.F3T_ByteCarrier.lift AspisR1.FIo_Install.W C
                                  (@AspisR1.FIp_Install.configuration C err c r)
                                  (@AspisR1.SCE_Experiment.submission A a))))
                            (@FS.emptyTable AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State)
                            AspisR1.RawRecordedOracleExtractionMassBin.failureMass)
                          (AspisR1.F3T_Numeric.accountLoss
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q0 Q1))))
                      (@LE.le.{0} Rat Rat.instLE (AspisR1.F3T_RuntimeBound.failureModel physical)
                        (AspisR1.F3T_Numeric.total
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q0 Q1))))
'AspisR1.NHZ_EXPERIMENT.same_law' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NIB_ReadToSettlement.read_to_settlement

```lean
@NIB_ReadToSettlement.read_to_settlement : ∀ {Invocation Context Key RuntimeState Accounts Other LaneImage : Type}
  [inst : DecidableEq.{1} Key] (runtime : NGK_NFO_PoolReturnData.Runtime Context Key RuntimeState),
  @NGK_NFR_PoolReturnData.RuntimeReturnData Context Key RuntimeState runtime →
    ∀ (emitInvocation poolInvocation : Invocation) (context : Invocation → Context) (program : Invocation → Key)
      (selected : Key) (readState : RuntimeState) (state after : AspisR1.S2I.ReturnData.State Accounts Other)
      (s : NFY_NEU_EmitModel.Statement),
      @Eq.{1} Invocation poolInvocation emitInvocation →
        @Eq.{1} Key (program emitInvocation) selected →
          @Eq.{1} RuntimeState readState
              (@NGK_NFO_PoolReturnData.Runtime.write Context Key RuntimeState runtime (context emitInvocation)
                (program emitInvocation)
                (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                  (fun l =>
                    @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                      (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 792) (instOfNatNat (nat_lit 792))) ⋯)))
                  (AspisR1.S2K.ResultPayload.bytes s))) →
            @Eq.{1}
                (Aeneas.Std.Result.{0}
                  (Aeneas.Std.core.result.Result.{0, 0} (AspisR1.S2I.ReturnData.State Accounts Other)
                    AdapterRw.solana_program_error.ProgramError))
                (@AspisR1.NFY_JHb_Emit.source Accounts Other
                  (fun st bytes =>
                    @Aeneas.Std.Result.ok.{0} (AspisR1.S2I.ReturnData.State Accounts Other)
                      (@AspisR1.S2I.ReturnData.set Accounts Other st bytes))
                  state s)
                (@Aeneas.Std.Result.ok.{0}
                  (Aeneas.Std.core.result.Result.{0, 0} (AspisR1.S2I.ReturnData.State Accounts Other)
                    AdapterRw.solana_program_error.ProgramError)
                  (@Aeneas.Std.core.result.Result.Ok.{0, 0} (AspisR1.S2I.ReturnData.State Accounts Other)
                    AdapterRw.solana_program_error.ProgramError after)) →
              ∀ (authenticated : NGK_NFO_ReadModel.Accepted) (events : List.{0} NGK_NFO_ReadModel.Event),
                @Eq.{1}
                    (Aeneas.Std.Result.{0}
                      (Prod.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error)
                        (List.{0} NGK_NFO_ReadModel.Event)))
                    (@NGK_NFO_ReadModel.run Key inst selected
                      (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit AdapterRw.solana_program_error.ProgramError
                        Unit.unit)
                      (@NGK_NFO_PoolReturnData.Runtime.read Context Key RuntimeState runtime (context poolInvocation)
                        readState)
                      NGK_NFO_PacketDecoder.run)
                    (@Aeneas.Std.Result.ok.{0}
                      (Prod.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error)
                        (List.{0} NGK_NFO_ReadModel.Event))
                      (@Prod.mk.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error)
                        (List.{0} NGK_NFO_ReadModel.Event)
                        (@Aeneas.Std.core.result.Result.Ok.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error
                          authenticated)
                        events)) →
                  ∀
                    (validate :
                      NGK_NFR_CSettlement.Output →
                        Aeneas.Std.Result.{0} (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_CSettlement.Error))
                    (lane :
                      NGK_NFR_CSettlement.Output →
                        Aeneas.Std.Result.{0}
                          (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_CSettlement.Error))
                    (image : LaneImage),
                    @Eq.{1}
                        (Aeneas.Std.Result.{0} (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_CSettlement.Error))
                        (validate authenticated.value)
                        (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_CSettlement.Error)
                          (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit NGK_NFR_CSettlement.Error Unit.unit)) →
                      @Eq.{1}
                          (Aeneas.Std.Result.{0}
                            (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_CSettlement.Error))
                          (lane authenticated.value)
                          (@Aeneas.Std.Result.ok.{0}
                            (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_CSettlement.Error)
                            (@Aeneas.Std.core.result.Result.Ok.{0, 0} LaneImage NGK_NFR_CSettlement.Error image)) →
                        And
                          (@Eq.{1}
                            (Aeneas.Std.Result.{0}
                              (Aeneas.Std.core.result.Result.{0, 0} Unit
                                AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
                            (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
                              s)
                            (@Aeneas.Std.Result.ok.{0}
                              (Aeneas.Std.core.result.Result.{0, 0} Unit
                                AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                              (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit
                                AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
                                Unit.unit)))
                          (And
                            (@Eq.{1}
                              (Aeneas.Std.Result.{0}
                                (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_CSettlement.Error))
                              (validate (AspisR1.S2K.ResultAdmission.value s))
                              (@Aeneas.Std.Result.ok.{0}
                                (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_CSettlement.Error)
                                (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit NGK_NFR_CSettlement.Error Unit.unit)))
                            (And
                              (@Eq.{1}
                                (Aeneas.Std.Result.{0}
                                  (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_CSettlement.Error))
                                (lane (AspisR1.S2K.ResultAdmission.value s))
                                (@Aeneas.Std.Result.ok.{0}
                                  (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_CSettlement.Error)
                                  (@Aeneas.Std.core.result.Result.Ok.{0, 0} LaneImage NGK_NFR_CSettlement.Error image)))
                              (And
                                (@Eq.{1} NGK_NFO_ReadModel.Output authenticated.value
                                  (AspisR1.S2K.ResultAdmission.value s))
                                (And
                                  (@Eq.{1} NGK_NFO_ReadModel.Bytes authenticated.bytes
                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                      (fun l =>
                                        @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                                          (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                                            (Aeneas.Std.Usize.ofNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 792) (instOfNatNat (nat_lit 792))) ⋯)))
                                      (AspisR1.S2K.ResultPayload.bytes s)))
                                  (And
                                    (@Eq.{1} (List.{0} NGK_NFO_ReadModel.Event) events
                                      (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.clear
                                        (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.invoke
                                          (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.read
                                            (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.decode
                                              (@List.nil.{0} NGK_NFO_ReadModel.Event))))))
                                    (And
                                      (@LE.le.{0} Nat instLENat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@List.length.{0} Aeneas.Std.U8 authenticated.bytes))
                                      (And
                                        (@LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U8 authenticated.bytes)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1024) (instOfNatNat (nat_lit 1024))))
                                        (And
                                          (@Eq.{1} (AspisR1.S2I.ReturnData.State Accounts Other) after
                                            (@AspisR1.S2I.ReturnData.set Accounts Other state
                                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                                (fun l =>
                                                  @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                                                    (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                                                      (Aeneas.Std.Usize.ofNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 792)
                                                          (instOfNatNat (nat_lit 792)))
                                                        ⋯)))
                                                (AspisR1.S2K.ResultPayload.bytes s))))
                                          (And
                                            (@Eq.{1}
                                              (Aeneas.Std.Result.{0}
                                                (Prod.{0, 0}
                                                  (Aeneas.Std.core.result.Result.{0, 0}
                                                    (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                                                    NGK_NFR_CSettlement.Error)
                                                  (List.{0} NGK_NFR_CSettlement.Call)))
                                              (@NGK_NFR_CSettlement.run LaneImage validate lane
                                                NFY_NEY_EmitComposed.encode authenticated)
                                              (@Aeneas.Std.Result.ok.{0}
                                                (Prod.{0, 0}
                                                  (Aeneas.Std.core.result.Result.{0, 0}
                                                    (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                                                    NGK_NFR_CSettlement.Error)
                                                  (List.{0} NGK_NFR_CSettlement.Call))
                                                (@Prod.mk.{0, 0}
                                                  (Aeneas.Std.core.result.Result.{0, 0}
                                                    (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                                                    NGK_NFR_CSettlement.Error)
                                                  (List.{0} NGK_NFR_CSettlement.Call)
                                                  (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                                                    (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                                                    NGK_NFR_CSettlement.Error
                                                    (@Prod.mk.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes image
                                                      (AspisR1.S2K.ResultPayload.bytes s)))
                                                  (@List.cons.{0} NGK_NFR_CSettlement.Call
                                                    (NGK_NFR_CSettlement.Call.validate authenticated.value)
                                                    (@List.cons.{0} NGK_NFR_CSettlement.Call
                                                      (NGK_NFR_CSettlement.Call.lane authenticated.value)
                                                      (@List.cons.{0} NGK_NFR_CSettlement.Call
                                                        (NGK_NFR_CSettlement.Call.encode authenticated.value)
                                                        (@List.nil.{0} NGK_NFR_CSettlement.Call)))))))
                                            (@Eq.{1}
                                              (Aeneas.Std.Result.{0}
                                                (Prod.{0, 0}
                                                  (Aeneas.Std.core.result.Result.{0, 0} NGK_NFV_HelperModel.Bytes
                                                    NGK_NFV_HelperModel.ProgramError)
                                                  (List.{0} NGK_NFV_HelperModel.Call)))
                                              (NGK_NFV_HelperModel.run NFY_NEY_EmitComposed.encode authenticated.value)
                                              (@Aeneas.Std.Result.ok.{0}
                                                (Prod.{0, 0}
                                                  (Aeneas.Std.core.result.Result.{0, 0} NGK_NFV_HelperModel.Bytes
                                                    NGK_NFV_HelperModel.ProgramError)
                                                  (List.{0} NGK_NFV_HelperModel.Call))
                                                (@Prod.mk.{0, 0}
                                                  (Aeneas.Std.core.result.Result.{0, 0} NGK_NFV_HelperModel.Bytes
                                                    NGK_NFV_HelperModel.ProgramError)
                                                  (List.{0} NGK_NFV_HelperModel.Call)
                                                  (@Aeneas.Std.core.result.Result.Ok.{0, 0} NGK_NFV_HelperModel.Bytes
                                                    NGK_NFV_HelperModel.ProgramError
                                                    (AspisR1.S2K.ResultPayload.bytes s))
                                                  (@List.cons.{0} NGK_NFV_HelperModel.Call
                                                    (NGK_NFV_HelperModel.Call.encode authenticated.value)
                                                    (@List.cons.{0} NGK_NFV_HelperModel.Call
                                                      (NGK_NFV_HelperModel.Call.allocate
                                                        (AspisR1.S2K.ResultPayload.bytes s))
                                                      (@List.nil.{0} NGK_NFV_HelperModel.Call)))))))))))))))
'NIB_ReadToSettlement.read_to_settlement' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NHW_WriterFromNative.under_retained_extraction

```lean
@AspisR1.NHW_WriterFromNative.under_retained_extraction : ∀ {A C : Type} (missing : AspisR1.IDa_Deployed.Uninstalled C)
  (err : C) (r : AspisR1.NP6_StdModel.Reservation) (n1 : AspisR1.S2W_ExtractionBoundary.First)
  (n2 : AspisR1.S2W_ExtractionBoundary.Second)
  (hashv : AspisR1.S2Z.Oracle.Parts → Aeneas.Std.Result.{0} AspisR1.S2Z.Oracle.Digest),
  AspisR1.S2W_DigestExtraction.AeneasExtraction
      (@AspisR1.DrvC_Installation.sdk AspisR1.FIo_Install.W C
        (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
      n1 n2 hashv →
    ∀
      (copy :
        AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
          Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record)),
      @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy →
        ∀ (allocator : AspisR1.S2W_D189Wrappers.Allocator A) (e1 : AspisR1.S2W_D189Entry.Entry)
          (id : AspisR1.S2W_ExtractionBoundary.Program) (data1 : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (state1 final1 : A)
          (saved : Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
          (post1 : AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)),
          @Eq.{1}
              (Aeneas.Std.Result.{0}
                (Aeneas.Std.core.result.Result.{0, 0}
                  (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                  AspisR1.AdapterRw.Cuts.PE))
              (@AspisR1.S2W_D189Wrappers.first A n1 copy allocator e1 id data1 state1)
              (@Aeneas.Std.Result.ok.{0}
                (Aeneas.Std.core.result.Result.{0, 0}
                  (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                  AspisR1.AdapterRw.Cuts.PE)
                (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                  (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                  AspisR1.AdapterRw.Cuts.PE
                  (@Prod.mk.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                    (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A) saved
                    (@Prod.mk.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A post1 final1)))) →
            ∃ semantic publicBytes proof split run,
              ∃ (domain :
                AspisR1.NGC_KNE_Caller.WriterDomain
                  (AspisR1.CheckpointBytes3Namespaces.toPrepared
                    (AspisR1.Tx1Q_Carriers.prepared
                      (@AspisR1.Tx1Q_Execution.Run.p C AdapterRw.SolanaDigest
                        (@AspisR1.DrvC_Installation.currentInstalled AspisR1.FIo_Install.W C
                          (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                        (@AspisR1.DrvC_Installation.Configuration.reserved AspisR1.FIo_Install.W C
                          (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                        (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W C
                          (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                        (@AspisR1.DrvC_Installation.Configuration.geometry AspisR1.FIo_Install.W C
                          (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                        (@AspisR1.DrvC_Installation.currentDigest AspisR1.FIo_Install.W C
                          (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                        Unit.unit (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes proof split saved run)))
                  (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                    (AspisR1.Tx1Q_Carriers.accumulator
                      (have __src :=
                        @AspisR1.Tx1Q_Execution.Run.out C AdapterRw.SolanaDigest
                          (@AspisR1.DrvC_Installation.currentInstalled AspisR1.FIo_Install.W C
                            (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                          (@AspisR1.DrvC_Installation.Configuration.reserved AspisR1.FIo_Install.W C
                            (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                          (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W C
                            (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                          (@AspisR1.DrvC_Installation.Configuration.geometry AspisR1.FIo_Install.W C
                            (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                          (@AspisR1.DrvC_Installation.currentDigest AspisR1.FIo_Install.W C
                            (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                          Unit.unit (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes proof split saved run;
                      {
                        weights :=
                          @Subtype.mk.{1} (List.{0} AspisR1CurrentCaller.aspis_core.field.QM31)
                            (fun l =>
                              @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1CurrentCaller.aspis_core.field.QM31 l)
                                Aeneas.Std.Usize.max)
                            (@Subtype.val.{1} (List.{0} AspisR1.Tx1Q_Carriers.C.K)
                              (fun l =>
                                @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1.Tx1Q_Carriers.C.K l)
                                  Aeneas.Std.Usize.max)
                              (@AspisR1.Tx1Q_Execution.Run.flushed C AdapterRw.SolanaDigest
                                (@AspisR1.DrvC_Installation.currentInstalled AspisR1.FIo_Install.W C
                                  (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                (@AspisR1.DrvC_Installation.Configuration.reserved AspisR1.FIo_Install.W C
                                  (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W C
                                  (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                (@AspisR1.DrvC_Installation.Configuration.geometry AspisR1.FIo_Install.W C
                                  (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                (@AspisR1.DrvC_Installation.currentDigest AspisR1.FIo_Install.W C
                                  (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                Unit.unit (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes proof split
                                saved run))
                            ⋯,
                        rhs := __src.rhs, power := __src.power, next := __src.next })))),
                ∃ hp hu hc,
                  And
                    (@Eq.{1}
                      (Aeneas.Std.Result.{0}
                        (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                          AdapterRw.solana_program_error.ProgramError))
                      (AdapterRw.first_decoded
                        (@AspisR1.DrvC_Installation.sdk AspisR1.FIo_Install.W C
                          (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                        semantic publicBytes proof split)
                      (@Aeneas.Std.Result.ok.{0}
                        (Aeneas.Std.core.result.Result.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                          AdapterRw.solana_program_error.ProgramError)
                        (@Aeneas.Std.core.result.Result.Ok.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                          AdapterRw.solana_program_error.ProgramError saved)))
                    (@Eq.{1}
                      (Aeneas.Std.Result.{0}
                        (Aeneas.Std.core.result.Result.{0, 0}
                          (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                            (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                          AspisR1.AdapterRw.Cuts.PE))
                      (@AspisR1.S2W_D189Wrappers.first A n1 copy allocator e1 id data1 state1)
                      (@Aeneas.Std.Result.ok.{0}
                        (Aeneas.Std.core.result.Result.{0, 0}
                          (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                            (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                          AspisR1.AdapterRw.Cuts.PE)
                        (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                          (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                            (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A))
                          AspisR1.AdapterRw.Cuts.PE
                          (@Prod.mk.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} Aeneas.Std.U8)
                            (Prod.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A)
                            (AspisR1.NGC_KNE_Writer.returned
                              (AspisR1.CheckpointBytes3Namespaces.toPrepared
                                (AspisR1.Tx1Q_Carriers.prepared
                                  (@AspisR1.Tx1Q_Execution.Run.p C AdapterRw.SolanaDigest
                                    (@AspisR1.DrvC_Installation.currentInstalled AspisR1.FIo_Install.W C
                                      (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                    (@AspisR1.DrvC_Installation.Configuration.reserved AspisR1.FIo_Install.W C
                                      (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                    (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W C
                                      (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                    (@AspisR1.DrvC_Installation.Configuration.geometry AspisR1.FIo_Install.W C
                                      (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                    (@AspisR1.DrvC_Installation.currentDigest AspisR1.FIo_Install.W C
                                      (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                    Unit.unit (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes proof split
                                    saved run)))
                              (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                                (AspisR1.Tx1Q_Carriers.accumulator
                                  (have __src :=
                                    @AspisR1.Tx1Q_Execution.Run.out C AdapterRw.SolanaDigest
                                      (@AspisR1.DrvC_Installation.currentInstalled AspisR1.FIo_Install.W C
                                        (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                      (@AspisR1.DrvC_Installation.Configuration.reserved AspisR1.FIo_Install.W C
                                        (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                      (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W C
                                        (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                      (@AspisR1.DrvC_Installation.Configuration.geometry AspisR1.FIo_Install.W C
                                        (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                      (@AspisR1.DrvC_Installation.currentDigest AspisR1.FIo_Install.W C
                                        (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                      Unit.unit (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes proof
                                      split saved run;
                                  {
                                    weights :=
                                      @Subtype.mk.{1} (List.{0} AspisR1CurrentCaller.aspis_core.field.QM31)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat
                                            (@List.length.{0} AspisR1CurrentCaller.aspis_core.field.QM31 l)
                                            Aeneas.Std.Usize.max)
                                        (@Subtype.val.{1} (List.{0} AspisR1.Tx1Q_Carriers.C.K)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1.Tx1Q_Carriers.C.K l)
                                              Aeneas.Std.Usize.max)
                                          (@AspisR1.Tx1Q_Execution.Run.flushed C AdapterRw.SolanaDigest
                                            (@AspisR1.DrvC_Installation.currentInstalled AspisR1.FIo_Install.W C
                                              (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                            (@AspisR1.DrvC_Installation.Configuration.reserved AspisR1.FIo_Install.W C
                                              (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                            (@AspisR1.DrvC_Installation.Configuration.query AspisR1.FIo_Install.W C
                                              (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                            (@AspisR1.DrvC_Installation.Configuration.geometry AspisR1.FIo_Install.W C
                                              (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                            (@AspisR1.DrvC_Installation.currentDigest AspisR1.FIo_Install.W C
                                              (@AspisR1.NHW_DeployedQuery.configuration C missing err r))
                                            Unit.unit (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes
                                            proof split saved run))
                                        ⋯,
                                    rhs := __src.rhs, power := __src.power, next := __src.next })))
                              domain hp hu hc)
                            (@Prod.mk.{0, 0} (AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record)) A post1
                              final1)))))
'AspisR1.NHW_WriterFromNative.under_retained_extraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

