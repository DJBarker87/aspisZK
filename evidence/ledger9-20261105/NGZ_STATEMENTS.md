# Exact kernel-loaded statements

Fresh full-name, explicit-argument and universe output from the SAME NGZ combined forest. These quotations do not discharge native/root hypotheses.

## AspisR1.NGR_HISTORY.saved_to_loaded

NGZ_L035. Exact statement and axioms:

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

NGZ_L035. Exact statement and axioms:

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

NGZ_L035. Exact statement and axioms:

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

NGZ_L035. Exact statement and axioms:

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

## AspisR1.RPx_Deployed.deployed

NGZ_L035. Exact statement and axioms:

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

## AspisR1.NGC_WriterDomain.from_query_loop

NGZ_L036. Exact statement and axioms:

```lean
AspisR1.NGC_WriterDomain.from_query_loop : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a after : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.wide_exact.WideExact
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b pending : AspisR1Stage2.verifier.BatchedWeights),
  AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) a b →
    @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      AspisR1.NGC_PreparationBoundary.Fields p →
        @Eq.{1}
            (Aeneas.Std.Result.{0}
              (Aeneas.Std.core.result.Result.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error))
            (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a
              g (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
              (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯))
            (@Aeneas.Std.Result.ok.{0}
              (Aeneas.Std.core.result.Result.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error)
              (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error
                (@Prod.mk.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights after
                  pending))) →
          ∃ out,
            And
              (@Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.Slice.{0} AspisR1.Port3_FlushInstall.K))
                (AspisR1.Port3_FlushInstall.flush pending
                  (@Aeneas.Std.alloc.vec.Vec.deref AspisR1Stage2.aspis_core.field.QM31 after.weights))
                (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.Slice.{0} AspisR1Stage2.aspis_core.field.QM31) out))
              (have written :=
                {
                  weights :=
                    @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                      (fun l =>
                        @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                          Aeneas.Std.Usize.max)
                      (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                        (fun l =>
                          @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                            Aeneas.Std.Usize.max)
                        out)
                      ⋯,
                  rhs := after.rhs, power := after.power, next := after.next };
              And
                (AspisR1.NGC_KNE_Caller.WriterDomain (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                  (AspisR1.CheckpointBytes3Namespaces.toAccumulator written))
                (And (@Eq.{1} AspisR1Stage2.aspis_core.field.wide_exact.WideExact written.rhs after.rhs)
                  (And (@Eq.{1} AspisR1Stage2.aspis_core.field.QM31 written.power after.power)
                    (@Eq.{1} Aeneas.Std.Usize written.next after.next))))
'AspisR1.NGC_WriterDomain.from_query_loop' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGC_CheckpointBridge.derived_packet

NGZ_L036. Exact statement and axioms:

```lean
AspisR1.NGC_CheckpointBridge.derived_packet : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a after : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.wide_exact.WideExact
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b pending : AspisR1Stage2.verifier.BatchedWeights),
  AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) a b →
    @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      AspisR1.NGC_PreparationBoundary.Fields p →
        @Eq.{1}
            (Aeneas.Std.Result.{0}
              (Aeneas.Std.core.result.Result.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error))
            (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a
              g (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
              (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯))
            (@Aeneas.Std.Result.ok.{0}
              (Aeneas.Std.core.result.Result.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error)
              (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error
                (@Prod.mk.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights after
                  pending))) →
          ∃ out,
            ∃ (writerDomain :
              AspisR1.NGC_KNE_Caller.WriterDomain (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                  {
                    weights :=
                      @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                        (fun l =>
                          @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                            Aeneas.Std.Usize.max)
                        (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                          (fun l =>
                            @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                              Aeneas.Std.Usize.max)
                          out)
                        ⋯,
                    rhs := after.rhs, power := after.power, next := after.next })),
              And
                (@Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.Slice.{0} AspisR1.Port3_FlushInstall.K))
                  (AspisR1.Port3_FlushInstall.flush pending
                    (@Aeneas.Std.alloc.vec.Vec.deref AspisR1Stage2.aspis_core.field.QM31 after.weights))
                  (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.Slice.{0} AspisR1Stage2.aspis_core.field.QM31) out))
                (And
                  (∀ (stored publicBytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8),
                    @Eq.{2} (AspisR1.CheckpointBytes5Effect.Code (Aeneas.Std.Slice.{0} Aeneas.Std.U8))
                      (AspisR1.NGC_KNE_Writer.sourceProgram (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                        (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                          {
                            weights :=
                              @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                                    Aeneas.Std.Usize.max)
                                (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                  (fun l =>
                                    @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                                      Aeneas.Std.Usize.max)
                                  out)
                                ⋯,
                            rhs := after.rhs, power := after.power, next := after.next })
                        writerDomain stored publicBytes)
                      (AspisR1.CheckpointBytes5Writer.writer (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                        (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                          {
                            weights :=
                              @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                                    Aeneas.Std.Usize.max)
                                (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                  (fun l =>
                                    @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                                      Aeneas.Std.Usize.max)
                                  out)
                                ⋯,
                            rhs := after.rhs, power := after.power, next := after.next })
                        stored publicBytes))
                  (∀ (hp hu hc : AspisR1.CheckpointBytes5Effect.Digest),
                    And
                      (@Eq.{1} Nat
                        (@List.length.{0} NGC_KND_Schedule.Step
                          (AspisR1.NGC_KNE_Schedule.derivedSchedule (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                            (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                              {
                                weights :=
                                  @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                    (fun l =>
                                      @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                                        Aeneas.Std.Usize.max)
                                    (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                      (fun l =>
                                        @LE.le.{0} Nat instLENat
                                          (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l) Aeneas.Std.Usize.max)
                                      out)
                                    ⋯,
                                rhs := after.rhs, power := after.power, next := after.next })
                            writerDomain hp hu hc))
                        (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                      (∀ (step : NGC_KND_Schedule.Step),
                        @Membership.mem.{0, 0} NGC_KND_Schedule.Step (List.{0} NGC_KND_Schedule.Step)
                            (@List.instMembership.{0} NGC_KND_Schedule.Step)
                            (AspisR1.NGC_KNE_Schedule.derivedSchedule (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                              (AspisR1.CheckpointBytes3Namespaces.toAccumulator
                                {
                                  weights :=
                                    @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                      (fun l =>
                                        @LE.le.{0} Nat instLENat
                                          (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l) Aeneas.Std.Usize.max)
                                      (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat
                                            (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                                            Aeneas.Std.Usize.max)
                                        out)
                                      ⋯,
                                  rhs := after.rhs, power := after.power, next := after.next })
                              writerDomain hp hu hc)
                            step →
                          @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) step.len step.size)
                            step.cap)))
'AspisR1.NGC_CheckpointBridge.derived_packet' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGC_PrestateBridge.from_initializers

NGZ_L036. Exact statement and axioms:

```lean
AspisR1.NGC_PrestateBridge.from_initializers : ∀ (constructors : VTop_Stages.Ops) (reserveA reserveB : Bool)
  (base : AspisR1.Port3_NativeQueryBody.Ops) (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
  (p : AspisR1Stage2.verifier.Prepared) (a after : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.wide_exact.WideExact
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b pending : AspisR1Stage2.verifier.BatchedWeights),
  AspisR1.NGC_PreparationBoundary.Fields p →
    @Eq.{1}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} VTop_Stages.verifier.Accumulator VTop_Stages.verifier.Error))
        ((AspisR1.Port3_Constructor.installed constructors reserveA).op12 AspisR1Stage2.transport.Variant.S2)
        (@Aeneas.Std.Result.ok.{0}
          (Aeneas.Std.core.result.Result.{0, 0} VTop_Stages.verifier.Accumulator VTop_Stages.verifier.Error)
          (@Aeneas.Std.core.result.Result.Ok.{0, 0} VTop_Stages.verifier.Accumulator VTop_Stages.verifier.Error a)) →
      @Eq.{1}
          (Aeneas.Std.Result.{0}
            (Aeneas.Std.core.result.Result.{0, 0} AspisR1Stage2.verifier.BatchedWeights VTop_Stages.verifier.Error))
          (AspisR1.Port3_NativePendingInstall.source reserveB
            (@Aeneas.Std.alloc.vec.Vec.deref AspisR1Stage2.aspis_core.field.QM31 a.weights))
          (@Aeneas.Std.Result.ok.{0}
            (Aeneas.Std.core.result.Result.{0, 0} AspisR1Stage2.verifier.BatchedWeights VTop_Stages.verifier.Error)
            (@Aeneas.Std.core.result.Result.Ok.{0, 0} AspisR1Stage2.verifier.BatchedWeights VTop_Stages.verifier.Error
              b)) →
        @Eq.{1}
            (Aeneas.Std.Result.{0}
              (Aeneas.Std.core.result.Result.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error))
            (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a
              g (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
              (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯))
            (@Aeneas.Std.Result.ok.{0}
              (Aeneas.Std.core.result.Result.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error)
              (@Aeneas.Std.core.result.Result.Ok.{0, 0}
                (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
                AspisR1Stage2.verifier.Error
                (@Prod.mk.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights after
                  pending))) →
          ∃ out,
            And
              (@Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.Slice.{0} AspisR1.Port3_FlushInstall.K))
                (AspisR1.Port3_FlushInstall.flush pending
                  (@Aeneas.Std.alloc.vec.Vec.deref AspisR1Stage2.aspis_core.field.QM31 after.weights))
                (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.Slice.{0} AspisR1Stage2.aspis_core.field.QM31) out))
              (have written :=
                {
                  weights :=
                    @Subtype.mk.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                      (fun l =>
                        @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                          Aeneas.Std.Usize.max)
                      (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.QM31)
                        (fun l =>
                          @LE.le.{0} Nat instLENat (@List.length.{0} AspisR1Stage2.aspis_core.field.QM31 l)
                            Aeneas.Std.Usize.max)
                        out)
                      ⋯,
                  rhs := after.rhs, power := after.power, next := after.next };
              And
                (AspisR1.NGC_KNE_Caller.WriterDomain (AspisR1.CheckpointBytes3Namespaces.toPrepared p)
                  (AspisR1.CheckpointBytes3Namespaces.toAccumulator written))
                (And (@Eq.{1} AspisR1Stage2.aspis_core.field.wide_exact.WideExact written.rhs after.rhs)
                  (And (@Eq.{1} AspisR1Stage2.aspis_core.field.QM31 written.power after.power)
                    (@Eq.{1} Aeneas.Std.Usize written.next after.next))))
'AspisR1.NGC_PrestateBridge.from_initializers' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NGK_NFR_ModelJoin.same_emitted_settlement

NGZ_L037. Exact statement and axioms:

```lean
@NGK_NFR_ModelJoin.same_emitted_settlement : ∀ {Context Key RuntimeState Accounts Other LaneImage : Type}
  [inst : DecidableEq.{1} Key] (runtime : NGK_NFO_PoolReturnData.Runtime Context Key RuntimeState),
  @NGK_NFR_PoolReturnData.RuntimeReturnData Context Key RuntimeState runtime →
    ∀ (context : Context) (selected : Key) (state : AspisR1.S2I.ReturnData.State Accounts Other)
      (s : NFY_NEU_EmitModel.Statement),
      @Eq.{1}
          (Aeneas.Std.Result.{0}
            (Aeneas.Std.core.result.Result.{0, 0} Unit
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
          (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s)
          (@Aeneas.Std.Result.ok.{0}
            (Aeneas.Std.core.result.Result.{0, 0} Unit
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
            (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit
              AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 Unit.unit)) →
        ∀
          (validate :
            NGK_NFR_ModelJoin.Output →
              Aeneas.Std.Result.{0} (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_ModelJoin.PoolError))
          (lane :
            NGK_NFR_ModelJoin.Output →
              Aeneas.Std.Result.{0} (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_ModelJoin.PoolError))
          (image : LaneImage),
          @Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_ModelJoin.PoolError))
              (validate (AspisR1.S2K.ResultAdmission.value s))
              (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.core.result.Result.{0, 0} Unit NGK_NFR_ModelJoin.PoolError)
                (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit NGK_NFR_ModelJoin.PoolError Unit.unit)) →
            @Eq.{1} (Aeneas.Std.Result.{0} (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_ModelJoin.PoolError))
                (lane (AspisR1.S2K.ResultAdmission.value s))
                (@Aeneas.Std.Result.ok.{0} (Aeneas.Std.core.result.Result.{0, 0} LaneImage NGK_NFR_ModelJoin.PoolError)
                  (@Aeneas.Std.core.result.Result.Ok.{0, 0} LaneImage NGK_NFR_ModelJoin.PoolError image)) →
              And
                (@Eq.{1}
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
                      AdapterRw.solana_program_error.ProgramError
                      (@AspisR1.S2I.ReturnData.set Accounts Other state
                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                          (fun l =>
                            @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                              (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                                (Aeneas.Std.Usize.ofNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 792) (instOfNatNat (nat_lit 792))) ⋯)))
                          (AspisR1.S2K.ResultPayload.bytes s))))))
                (And
                  (@Eq.{1}
                    (Aeneas.Std.Result.{0}
                      (Prod.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error)
                        (List.{0} NGK_NFO_ReadModel.Event)))
                    (@NGK_NFO_ReadModel.run Key inst selected
                      (@Aeneas.Std.core.result.Result.Ok.{0, 0} Unit AdapterRw.solana_program_error.ProgramError
                        Unit.unit)
                      (@NGK_NFO_PoolReturnData.Runtime.read Context Key RuntimeState runtime context
                        (@NGK_NFO_PoolReturnData.Runtime.write Context Key RuntimeState runtime context selected
                          (@Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                            (fun l =>
                              @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                                (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                                  (Aeneas.Std.Usize.ofNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 792) (instOfNatNat (nat_lit 792))) ⋯)))
                            (AspisR1.S2K.ResultPayload.bytes s))))
                      NGK_NFO_PacketDecoder.run)
                    (@Aeneas.Std.Result.ok.{0}
                      (Prod.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error)
                        (List.{0} NGK_NFO_ReadModel.Event))
                      (@Prod.mk.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error)
                        (List.{0} NGK_NFO_ReadModel.Event)
                        (@Aeneas.Std.core.result.Result.Ok.{0, 0} NGK_NFO_ReadModel.Accepted NGK_NFO_ReadModel.Error
                          { value := AspisR1.S2K.ResultAdmission.value s,
                            bytes :=
                              @Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                                (fun l =>
                                  @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                                    (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                                      (Aeneas.Std.Usize.ofNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 792) (instOfNatNat (nat_lit 792))) ⋯)))
                                (AspisR1.S2K.ResultPayload.bytes s) })
                        (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.clear
                          (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.invoke
                            (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.read
                              (@List.cons.{0} NGK_NFO_ReadModel.Event NGK_NFO_ReadModel.Event.decode
                                (@List.nil.{0} NGK_NFO_ReadModel.Event))))))))
                  (@Eq.{1}
                    (Aeneas.Std.Result.{0}
                      (Prod.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                          NGK_NFR_CSettlement.Error)
                        (List.{0} NGK_NFR_CSettlement.Call)))
                    (@NGK_NFR_CSettlement.run LaneImage validate lane NFY_NEY_EmitComposed.encode
                      { value := AspisR1.S2K.ResultAdmission.value s,
                        bytes :=
                          @Subtype.val.{1} (List.{0} Aeneas.Std.U8)
                            (fun l =>
                              @Eq.{1} Nat (@List.length.{0} Aeneas.Std.U8 l)
                                (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize
                                  (Aeneas.Std.Usize.ofNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 792) (instOfNatNat (nat_lit 792))) ⋯)))
                            (AspisR1.S2K.ResultPayload.bytes s) })
                    (@Aeneas.Std.Result.ok.{0}
                      (Prod.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                          NGK_NFR_CSettlement.Error)
                        (List.{0} NGK_NFR_CSettlement.Call))
                      (@Prod.mk.{0, 0}
                        (Aeneas.Std.core.result.Result.{0, 0} (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                          NGK_NFR_CSettlement.Error)
                        (List.{0} NGK_NFR_CSettlement.Call)
                        (@Aeneas.Std.core.result.Result.Ok.{0, 0} (Prod.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes)
                          NGK_NFR_CSettlement.Error
                          (@Prod.mk.{0, 0} LaneImage NGK_NFR_CSettlement.Bytes image
                            (AspisR1.S2K.ResultPayload.bytes s)))
                        (@List.cons.{0} NGK_NFR_CSettlement.Call
                          (NGK_NFR_CSettlement.Call.validate (AspisR1.S2K.ResultAdmission.value s))
                          (@List.cons.{0} NGK_NFR_CSettlement.Call
                            (NGK_NFR_CSettlement.Call.lane (AspisR1.S2K.ResultAdmission.value s))
                            (@List.cons.{0} NGK_NFR_CSettlement.Call
                              (NGK_NFR_CSettlement.Call.encode (AspisR1.S2K.ResultAdmission.value s))
                              (@List.nil.{0} NGK_NFR_CSettlement.Call))))))))
'NGK_NFR_ModelJoin.same_emitted_settlement' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NGM_GuardRawModel.cohort

NGZ_L038. Exact statement and axioms:

```lean
NGM_GuardRawModel.cohort : ∀ (w : FIo_Native.weights.Weights) (folds : Aeneas.Std.Usize),
  @Eq.{1} (Aeneas.Std.Result.{0} Bool)
    (NGM_GuardRef.guard_raw_ref (NGM_GuardRawModel.variant w.variant) folds
      (NGM_GuardRawModel.rowArray
        (NGM_GuardExact.row w
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 0)))
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 2)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 2)))))
      (NGM_GuardRawModel.rowArray
        (NGM_GuardExact.row w
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 2)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 2)))
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 2)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 2)))))
      (NGM_GuardRawModel.rowArray
        (NGM_GuardExact.row w
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 0)))
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 3)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 3)))))
      (NGM_GuardRawModel.rowArray
        (NGM_GuardExact.row w
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 2)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 2)))
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 3)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯ (nat_lit 3))))))
    (FIo_Native.weights.shared_two_point_guard w folds)
'NGM_GuardRawModel.cohort' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NGM_GuardExact.source

NGZ_L038. Exact statement and axioms:

```lean
NGM_GuardExact.source : ∀ (w : FIo_Native.weights.Weights) (folds : Aeneas.Std.Usize),
  @Eq.{1} (Aeneas.Std.Result.{0} Bool) (FIo_Native.weights.shared_two_point_guard w folds)
    (@Aeneas.Std.Result.ok.{0} Bool (NGM_GuardExact.guard w folds))
'NGM_GuardExact.source' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NGM_DoubleProduct.cohort

NGZ_L038. Exact statement and axioms:

```lean
NGM_DoubleProduct.cohort : ∀ (x : NGM_ProbeTransport.FQ),
  NGM_DoubleProduct.Canonical x →
    ∃ product,
      And
        (@Eq.{1} (Aeneas.Std.Result.{0} FIn_WeightsExtract.field.QM31) (FIn_WeightsExtract.field.QM31.mul x x)
          (@Aeneas.Std.Result.ok.{0} NGM_ProbeTransport.FQ product))
        (And (NGM_DoubleProduct.Canonical product)
          (And
            (@Eq.{1} AspisR1.LPi_FieldValues.QW (AspisR1.LPi_FieldValues.qw (NGM_ProbeTransport.toQ product))
              (AspisR1.LPi_FieldValues.mulQ (AspisR1.LPi_FieldValues.qw (NGM_ProbeTransport.toQ x))
                (AspisR1.LPi_FieldValues.qw (NGM_ProbeTransport.toQ x))))
            (@Eq.{1}
              (Aeneas.Std.Result.{0}
                (Aeneas.Std.Array.{0} Aeneas.Std.U32
                  (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ⋯)))
              (NGM_DoubleRef.double_observed_ref (NGM_DoubleModel.words product) (NGM_DoubleModel.words product))
              (@Bind.bind.{0, 0} Aeneas.Std.Result.{0} Aeneas.Std.instBindResult.{0} FIn_WeightsExtract.field.QM31
                (Aeneas.Std.Array.{0} Aeneas.Std.U32
                  (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ⋯))
                (FIn_WeightsExtract.double x) fun out =>
                @Aeneas.Std.Result.ok.{0}
                  (Aeneas.Std.Array.{0} Aeneas.Std.U32
                    (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ⋯))
                  (NGM_DoubleModel.words out)))))
'NGM_DoubleProduct.cohort' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NGM_QueryExit.tx2

NGZ_L038. Exact statement and axioms:

```lean
AspisR1.NGM_QueryExit.tx2 : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops) (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
  (p : AspisR1Stage2.verifier.Prepared) (a after : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.wide_exact.WideExact
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b pending : AspisR1Stage2.verifier.BatchedWeights),
  AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) a b →
    @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
      @Eq.{1}
          (Aeneas.Std.Result.{0}
            (Aeneas.Std.core.result.Result.{0, 0}
              (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
              AspisR1Stage2.verifier.Error))
          (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a g
            (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
          (@Aeneas.Std.Result.ok.{0}
            (Aeneas.Std.core.result.Result.{0, 0}
              (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
              AspisR1Stage2.verifier.Error)
            (@Aeneas.Std.core.result.Result.Ok.{0, 0}
              (Prod.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights)
              AspisR1Stage2.verifier.Error
              (@Prod.mk.{0, 0} AspisR1Stage2.verifier.Accumulator AspisR1Stage2.verifier.BatchedWeights after
                pending))) →
        And
          (AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
            (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) after pending)
          (@Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize after.next)
            (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
'AspisR1.NGM_QueryExit.tx2' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NEX_PublicModel.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NEX_PublicModel.result_state_effects : ∀ {State : Type} (bytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
  (state : State),
  @Eq.{1}
    (Prod.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} NFY_NEX_PublicModel.Statement NFY_NEX_PublicModel.PE))
      (Prod.{0, 0} State (List.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} NFY_NEX_PublicModel.Statement NFY_NEX_PublicModel.PE))
      (Prod.{0, 0} State (List.{0} Unit)) (NFY_NEX_PublicModel.run bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisS6CurrentCodecInstallation.Statement
          AspisS6CurrentCodecInstallation.PE))
      (Prod.{0, 0} State (List.{0} Unit)) (AspisS6CurrentCodecInstallation.decode bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
'NFY_NEX_PublicModel.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NEM_ValidatorComposed.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NEM_ValidatorComposed.result_state_effects : ∀ {State : Type} (s : NFY_NBN_StatementResult.Statement)
  (state : State),
  have observed :=
    NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane NFY_NEM_LateOracle.late s;
  @Eq.{1} (Prod.{0, 0} NFY_NED_ValidatorTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call)))
    (@Prod.mk.{0, 0} NFY_NED_ValidatorTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call))
      (@Prod.fst.{0, 0} NFY_NED_ValidatorTrace.R (List.{0} NFY_NED_ValidatorTrace.Call) observed)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_ValidatorTrace.R (List.{0} NFY_NED_ValidatorTrace.Call) observed)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} Unit
          AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))
      (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call))
      (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_ValidatorTrace.R (List.{0} NFY_NED_ValidatorTrace.Call)
          (NFY_NED_ValidatorTrace.run s))))
'NFY_NEM_ValidatorComposed.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NEQ_EncoderOracle.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NEQ_EncoderOracle.result_state_effects : ∀ {State : Type} (s : NFY_NBN_StatementResult.Statement) (state : State),
  have observed :=
    NFY_NEQ_EncoderOracle.run
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
      s;
  @Eq.{1} (Prod.{0, 0} NFY_NED_EncoderTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call)))
    (@Prod.mk.{0, 0} NFY_NED_EncoderTrace.R (Prod.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call))
      (@Prod.fst.{0, 0} NFY_NED_EncoderTrace.R (List.{0} NFY_NED_EncoderTrace.Call) observed)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_EncoderTrace.R (List.{0} NFY_NED_EncoderTrace.Call) observed)))
    (@Prod.mk.{0, 0} NFY_NBN_StatementEncoderSummary.BytesResult
      (Prod.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call))
      (NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s))
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_EncoderTrace.Call) state
        (@Prod.snd.{0, 0} NFY_NED_EncoderTrace.R (List.{0} NFY_NED_EncoderTrace.Call) (NFY_NED_EncoderTrace.run s))))
'NFY_NEQ_EncoderOracle.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NEU_ReconstructAdopted.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NEU_ReconstructAdopted.result_state_effects : ∀ {State : Type} (request : NFY_NEU_ReconstructAdopted.Request)
  (a : NFY_NEU_ReconstructAdopted.Auth) (c : NFY_NEU_ReconstructAdopted.Candidate) (state : State),
  @Eq.{1}
    (Prod.{0, 0} (Aeneas.Std.Result.{0} NFY_NDM_CohortStatement.Reply)
      (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call)))
    (@NFY_NEU_ReconstructAdopted.run State request a c state)
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0}
          AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
          AdapterRw.solana_program_error.ProgramError))
      (Prod.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call)) (AspisR1.NFY_JHf_ReconstructionSlot.source request a c)
      (@Prod.mk.{0, 0} State (List.{0} NFY_NED_ValidatorTrace.Call) state
        (NFY_NEU_ReconstructCore.trace (AspisR1.JHf_Carrier.toRequest request)
          (AspisR1.JHf_Carrier.toAuthenticatedAsq8Accounts a)
          (AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 c))))
'NFY_NEU_ReconstructAdopted.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NFD_RequestOracle.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NFD_RequestOracle.result_state_effects : ∀ {State : Type} (bytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8)
  (state : State),
  @Eq.{1}
    (Prod.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisR1.NFY_JHd_RequestNative.Request
          AspisR1.NFY_JHd_RequestNative.FormatError))
      (Prod.{0, 0} State (List.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisR1.NFY_JHd_RequestNative.Request
          AspisR1.NFY_JHd_RequestNative.FormatError))
      (Prod.{0, 0} State (List.{0} Unit)) (NFY_NFD_RequestOracle.runSlice bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
    (@Prod.mk.{0, 0}
      (Aeneas.Std.Result.{0}
        (Aeneas.Std.core.result.Result.{0, 0} AspisR1.NFY_JHd_RequestNative.Request
          AspisR1.NFY_JHd_RequestNative.FormatError))
      (Prod.{0, 0} State (List.{0} Unit)) (AspisR1.NFY_JHd_RequestNative.decode bytes)
      (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
'NFY_NFD_RequestOracle.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NFJ_Scanner.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NFJ_Scanner.result_state_effects : ∀ {State : Type} (bytes : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (state : State)
  (reply : List.{0} Aeneas.Std.U8 → List.{0} Aeneas.Std.U8 → Int),
  NFY_NFJ_Comparison.RuntimeMemcmp reply →
    @Eq.{1}
      (Prod.{0, 0}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ScannedAsqaProof
            AdapterRw.solana_program_error.ProgramError))
        (Prod.{0, 0} State (List.{0} Unit)))
      (@Prod.mk.{0, 0}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ScannedAsqaProof
            AdapterRw.solana_program_error.ProgramError))
        (Prod.{0, 0} State (List.{0} Unit)) (NFY_NFJ_Scanner.run reply bytes)
        (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
      (@Prod.mk.{0, 0}
        (Aeneas.Std.Result.{0}
          (Aeneas.Std.core.result.Result.{0, 0} AdapterRw.r1_pool_adapter.ScannedAsqaProof
            AdapterRw.solana_program_error.ProgramError))
        (Prod.{0, 0} State (List.{0} Unit)) (AspisR1.NFY_JHf_Scan.source bytes)
        (@Prod.mk.{0, 0} State (List.{0} Unit) state (@List.nil.{0} Unit)))
'NFY_NFJ_Scanner.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFY_NEY_EmitComposed.result_state_effects

NGZ_L039. Exact statement and axioms:

```lean
@NFY_NEY_EmitComposed.result_state_effects : ∀ {A E : Type} (state : AspisR1.S2I.ReturnData.State A E)
  (s : NFY_NEU_EmitModel.Statement),
  @Eq.{1}
    (Aeneas.Std.Result.{0}
      (Aeneas.Std.core.result.Result.{0, 0} (AspisR1.S2I.ReturnData.State A E) NFY_NEU_EmitModel.ProgramError))
    (@NFY_NEU_EmitModel.run A E
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
      NFY_NEY_EmitComposed.encode
      (fun st bytes =>
        @Aeneas.Std.Result.ok.{0} (AspisR1.S2I.ReturnData.State A E) (@AspisR1.S2I.ReturnData.set A E st bytes))
      state s)
    (@AspisR1.NFY_JHb_Emit.source A E
      (fun st bytes =>
        @Aeneas.Std.Result.ok.{0} (AspisR1.S2I.ReturnData.State A E) (@AspisR1.S2I.ReturnData.set A E st bytes))
      state s)
'NFY_NEY_EmitComposed.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NFS_QueryLoopRoot.tx1

NGZ_L040. Exact statement and axioms:

```lean
AspisR1.NFS_QueryLoopRoot.tx1 : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b : AspisR1Stage2.verifier.BatchedWeights) (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) a b →
      @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.NFG_QueryLoopDefs.State)
          (AspisR1.NFG_QueryLoopDefs.run (AspisR1.NFS_QueryLoopRoot.child base proof p g geometry qPlace gPlace)
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯)
            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
            (@Aeneas.Std.core.result.Result.Ok.{0, 0}
              (Prod.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B) AspisR1Stage2.verifier.Error
              (@Prod.mk.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B a b)))
          (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a g
            (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) ⋯))
'AspisR1.NFS_QueryLoopRoot.tx1' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NFS_QueryLoopRoot.tx2

NGZ_L040. Exact statement and axioms:

```lean
AspisR1.NFS_QueryLoopRoot.tx2 : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (b : AspisR1Stage2.verifier.BatchedWeights) (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_QueryInvariant.Domain p (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) a b →
      @Eq.{1} Nat (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize a.next)
          (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
        @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.NFG_QueryLoopDefs.State)
          (AspisR1.NFG_QueryLoopDefs.run (AspisR1.NFS_QueryLoopRoot.child base proof p g geometry qPlace gPlace)
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯)
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
            (@Aeneas.Std.core.result.Result.Ok.{0, 0}
              (Prod.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B) AspisR1Stage2.verifier.Error
              (@Prod.mk.{0, 0} AspisR1.NFG_QueryLoopDefs.A AspisR1.NFG_QueryLoopDefs.B a b)))
          (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop (AspisR1.NFS_QueryOps.installed base) proof p a g
            (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry b
            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
'AspisR1.NFS_QueryLoopRoot.tx2' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NFS_QueryValuesPacket.source

NGZ_L040. Exact statement and axioms:

```lean
AspisR1.NFS_QueryValuesPacket.source : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : AspisR1Stage2.verifier.BatchedWeights)
  (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_AccumDomain.Input p a pending →
      @Eq.{1} (AspisR1.NFP_TraceTypes.M AspisR1.NFP_QueryCuts.Out)
        (AspisR1.NFS_QueryValuesPacket.run base proof p a g geometry pending qPlace gPlace)
        (AspisR1.NFP_QueryTrace.run (AspisR1.NFS_QueryOps.installed base) proof p a g geometry pending)
'AspisR1.NFS_QueryValuesPacket.source' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## AspisR1.NFS_QueryValuesPacket.result

NGZ_L040. Exact statement and axioms:

```lean
AspisR1.NFS_QueryValuesPacket.result : ∀ (base : AspisR1.Port3_NativeQueryBody.Ops)
  (proof : Aeneas.Std.Slice.{0} Aeneas.Std.U8) (p : AspisR1Stage2.verifier.Prepared)
  (a : AspisR1Stage2.verifier.Accumulator)
  (g :
    Aeneas.Std.Array.{0} AspisR1.NFP_QueryCuts.E
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))) ⋯))
  (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : AspisR1Stage2.verifier.BatchedWeights)
  (qPlace gPlace : Nat),
  NEV_DotInputs.Canonical
      (@AspisR1.FIp_DotsAdapter.toArray
        (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))
          NEV_DotInputs.Coefficients._proof_1)
        g) →
    AspisR1.NFS_AccumDomain.Input p a pending →
      @Eq.{1} (Aeneas.Std.Result.{0} AspisR1.NFP_QueryCuts.Out)
        (@AspisR1.NFI_TraceResult.M.result AspisR1.NFP_TraceTypes.Event AspisR1.NFP_QueryCuts.Out
          (AspisR1.NFS_QueryValuesPacket.run base proof p a g geometry pending qPlace gPlace))
        (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_values (AspisR1.NFS_QueryOps.installed base) proof p a g
          (@Option.none.{0} (AspisR1Stage2.verifier.Phase → Aeneas.Std.Result.{0} Unit)) geometry pending)
'AspisR1.NFS_QueryValuesPacket.result' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFN_NFB_GeometryComposed.result_state_effects

NGZ_L040. Exact statement and axioms:

```lean
@NFN_NFB_GeometryComposed.result_state_effects : ∀ {State Event : Type}
  (queries :
    Aeneas.Std.Array.{0} Aeneas.Std.U32
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
  (start finish : Aeneas.Std.Usize) (state : State),
  @Eq.{1}
    (Aeneas.Std.Result.{0}
      (Prod.{0, 0} (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G VTop_Stages.verifier.Error)
        (Prod.{0, 0} State (List.{0} Event))))
    (@NEB_PureFrame.run
      (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G VTop_Stages.verifier.Error) State Event
      state
      (@AspisR1.Port3_QueryInstall.result NFN_NEW_GeometryRawInterface.O.G
        (@AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap
          (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.N.G NFN_NEW_GeometryRawInterface.N.E)
          (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G AspisR1Stage2.verifier.Error)
          NFN_NEW_GeometryRawInterface.answer
          (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))))
    (@NEB_PureFrame.run
      (Aeneas.Std.core.result.Result.{0, 0} AspisR1Stage2.verifier.QueryGeometry VTop_Stages.verifier.Error) State Event
      state
      (@AspisR1.Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.CE NFN_NEW_GeometryDictionary.adopted queries
        start finish))
'NFN_NFB_GeometryComposed.result_state_effects' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

## NFN_NFB_GeometryComposed.accepted_physical

NGZ_L040. Exact statement and axioms:

```lean
NFN_NFB_GeometryComposed.accepted_physical : ∀
  (queries :
    Aeneas.Std.Array.{0} Aeneas.Std.U32
      (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) ⋯))
  (start finish : Aeneas.Std.Usize),
  NFN_NFB_RangeTrace.Deployed start finish →
    ∀ (heap : NFN_NFB_PhysicalFrame.Heap) (out : AspisR1Stage2.verifier.QueryGeometry),
      @Eq.{1}
          (Aeneas.Std.Result.{0}
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E))
          (@AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.N.G NFN_NEW_GeometryRawInterface.N.E)
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E)
            NFN_NEW_GeometryRawInterface.answer
            (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))
          (@Aeneas.Std.Result.ok.{0}
            (Aeneas.Std.core.result.Result.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E)
            (@Aeneas.Std.core.result.Result.Ok.{0, 0} NFN_NEW_GeometryRawInterface.O.G NFN_NEW_GeometryRawInterface.O.E
              out)) →
        ∃ rows lines flat prefixes product suffix resized inverse groups,
          And
            (@Eq.{1} Nat (@List.length.{0} NFN_NFB_GatherTrace.Row rows)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize finish)
                (@Aeneas.Std.UScalar.val Aeneas.Std.UScalarTy.Usize start)))
            (And
              (@Eq.{1} (List.{0} Aeneas.Std.U32)
                (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                  (fun l => @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max) flat)
                (@List.flatMap.{0, 0} NFN_NFB_GatherTrace.Row AspisR1.Port4C_GeometryGather.M
                  (fun r => AspisR1.Port4C_GeometryGather.Row.words r) rows))
              (And
                (@Eq.{1} (List.{0} Aeneas.Std.U32)
                  (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                    (fun l => @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max) lines)
                  (@List.map.{0, 0} NFN_NFB_GatherTrace.Row AspisR1.Port4C_GeometryGather.M (fun r => r.lineZ) rows))
                (And (@Eq.{1} Aeneas.Std.Usize out.start start)
                  (And (@Eq.{1} (Aeneas.Std.alloc.vec.Vec.{0} AspisR1Stage2.aspis_core.field.M31) out.line_z lines)
                    (And
                      (@Eq.{1}
                        (Aeneas.Std.alloc.vec.Vec.{0}
                          (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                            (Aeneas.Std.Usize.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                        out.inverses groups)
                      (And
                        (@Eq.{1}
                          (Aeneas.Std.Result.{0}
                            (Prod.{0, 0} (Aeneas.Std.alloc.vec.Vec.{0} AspisR1Stage2.aspis_core.field.M31)
                              AspisR1Stage2.aspis_core.field.M31))
                          (@AspisR1.Port3_NativeGeometryBody.Ops.op13 NFN_NEW_GeometryDictionary.CE
                            NFN_NEW_GeometryDictionary.adopted (@Aeneas.Std.alloc.vec.Vec.deref Aeneas.Std.U32 flat))
                          (@Aeneas.Std.Result.ok.{0} (Prod.{0, 0} NFN_NFB_GatherTrace.Vec Aeneas.Std.U32)
                            (@Prod.mk.{0, 0} NFN_NFB_GatherTrace.Vec Aeneas.Std.U32 prefixes product)))
                        (And
                          (@Eq.{1} Nat
                            (@List.length.{0} Aeneas.Std.U32
                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max)
                                prefixes))
                            (@List.length.{0} Aeneas.Std.U32
                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                (fun l =>
                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max)
                                flat)))
                          (And
                            (@Eq.{1} (Aeneas.Std.Result.{0} AspisR1Stage2.aspis_core.field.M31)
                              (@AspisR1.Port3_NativeGeometryBody.Ops.op11 NFN_NEW_GeometryDictionary.CE
                                NFN_NEW_GeometryDictionary.adopted product)
                              (@Aeneas.Std.Result.ok.{0} Aeneas.Std.U32 suffix))
                            (And
                              (@Eq.{1} (List.{0} Aeneas.Std.U32)
                                (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                  (fun l =>
                                    @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l) Aeneas.Std.Usize.max)
                                  resized)
                                (@List.replicate.{0} (Aeneas.Std.UScalar Aeneas.Std.UScalarTy.U32)
                                  (@List.length.{0} Aeneas.Std.U32
                                    (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                      (fun l =>
                                        @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                          Aeneas.Std.Usize.max)
                                      flat))
                                  (Aeneas.Std.U32.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                    ⋯)))
                              (And
                                (@Eq.{1}
                                  (Aeneas.Std.Result.{0}
                                    (Aeneas.Std.alloc.vec.Vec.{0} NEW_GeometryActual.aspis_core.field.M31))
                                  (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0
                                    (AspisR1.Port4C_Reverse.reverse
                                      (@Aeneas.Std.alloc.vec.Vec.len.{0} Aeneas.Std.U32 flat))
                                    flat prefixes suffix resized)
                                  (@Aeneas.Std.Result.ok.{0} NFN_NFB_GatherTrace.Vec inverse))
                                (And
                                  (@Eq.{1} Nat
                                    (@List.length.{0} Aeneas.Std.U32
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        inverse))
                                    (@List.length.{0} Aeneas.Std.U32
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        flat)))
                                  (And
                                    (NFN_NEW_GeometryReverse.Trace
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        flat)
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        prefixes)
                                      (@List.length.{0} Aeneas.Std.U32
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          flat))
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        resized)
                                      suffix
                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                        (fun l =>
                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                            Aeneas.Std.Usize.max)
                                        inverse)
                                      (NFN_NEW_GeometryReverse.suffixAfter
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          flat)
                                        (@List.length.{0} Aeneas.Std.U32
                                          (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                            (fun l =>
                                              @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                Aeneas.Std.Usize.max)
                                            flat))
                                        suffix)
                                      (NFN_NEW_GeometryReverse.callLog
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          flat)
                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                              Aeneas.Std.Usize.max)
                                          prefixes)
                                        (@List.length.{0} Aeneas.Std.U32
                                          (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                            (fun l =>
                                              @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                Aeneas.Std.Usize.max)
                                            flat))
                                        suffix))
                                    (And
                                      (@Eq.{1}
                                        (List.{0}
                                          (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                            (Aeneas.Std.Usize.ofNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                        (@Subtype.val.{1}
                                          (List.{0}
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                          (fun l =>
                                            @LE.le.{0} Nat instLENat
                                              (@List.length.{0}
                                                (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                  (Aeneas.Std.Usize.ofNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                                l)
                                              Aeneas.Std.Usize.max)
                                          out.inverses)
                                        (@List.map.{0, 0} Nat AspisR1.Port4C_CollectLoop.Group
                                          (AspisR1.Port4C_CollectLoop.record inverse)
                                          (List.range
                                            (@List.length.{0} Aeneas.Std.U32
                                              (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                    Aeneas.Std.Usize.max)
                                                lines)))))
                                      (And
                                        (@Eq.{1}
                                          (NFN_NFB_CollectorTrace.Guard
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                          (@NFN_NFB_CollectorTrace.finish
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                            (@NFN_NFB_CollectorTrace.fill
                                              (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                (Aeneas.Std.Usize.ofNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                              (@Subtype.val.{1}
                                                (List.{0}
                                                  (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                    (Aeneas.Std.Usize.ofNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat
                                                    (@List.length.{0}
                                                      (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                        (Aeneas.Std.Usize.ofNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                          ⋯))
                                                      l)
                                                    Aeneas.Std.Usize.max)
                                                out.inverses)
                                              (@NFN_NFB_CollectorTrace.Guard.mk
                                                (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                  (Aeneas.Std.Usize.ofNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                                (@List.nil.{0}
                                                  (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                    (Aeneas.Std.Usize.ofNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                          (@NFN_NFB_CollectorTrace.Guard.mk
                                            (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                              (Aeneas.Std.Usize.ofNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                            (@Subtype.val.{1}
                                              (List.{0}
                                                (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                  (Aeneas.Std.Usize.ofNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                              (fun l =>
                                                @LE.le.{0} Nat instLENat
                                                  (@List.length.{0}
                                                    (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                      (Aeneas.Std.Usize.ofNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                        ⋯))
                                                    l)
                                                  Aeneas.Std.Usize.max)
                                              out.inverses)
                                            (@List.length.{0}
                                              (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                (Aeneas.Std.Usize.ofNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯))
                                              (@Subtype.val.{1}
                                                (List.{0}
                                                  (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                    (Aeneas.Std.Usize.ofNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) ⋯)))
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat
                                                    (@List.length.{0}
                                                      (Aeneas.Std.Array.{0} AspisR1Stage2.aspis_core.field.M31
                                                        (Aeneas.Std.Usize.ofNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                          ⋯))
                                                      l)
                                                    Aeneas.Std.Usize.max)
                                                out.inverses))))
                                        (And
                                          (@Eq.{1} (Option.{0} (List.{0} Aeneas.Std.U32))
                                            (NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows)
                                              (NFN_NFB_ReturnedBuffers.initial heap)
                                              NFN_NFB_PrivateFrame.Place.lines.id)
                                            (@Option.some.{0} (List.{0} AspisR1Stage2.aspis_core.field.M31)
                                              (@Subtype.val.{1} (List.{0} AspisR1Stage2.aspis_core.field.M31)
                                                (fun l =>
                                                  @LE.le.{0} Nat instLENat
                                                    (@List.length.{0} AspisR1Stage2.aspis_core.field.M31 l)
                                                    Aeneas.Std.Usize.max)
                                                out.line_z)))
                                          (And
                                            (∀ (count : Nat),
                                              @Eq.{1} (Option.{0} (List.{0} Aeneas.Std.U32))
                                                (NFN_NFB_PhysicalFrame.run
                                                  (@List.take.{0} NFN_NFB_PhysicalFrame.Action count
                                                    (NFN_NFB_GatherFrame.actions rows))
                                                  (NFN_NFB_ReturnedBuffers.initial heap)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (heap (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                            (∀ (count : Nat),
                                              @Eq.{1} (Option.{0} (List.{0} Aeneas.Std.U32))
                                                (NFN_NFB_PhysicalFrame.run
                                                  (@List.take.{0} NFN_NFB_PhysicalFrame.Action count
                                                    (NFN_NFB_TerminalFrame.actions
                                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                        (fun l =>
                                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                            Aeneas.Std.Usize.max)
                                                        flat)
                                                      (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                        (fun l =>
                                                          @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                            Aeneas.Std.Usize.max)
                                                        prefixes)
                                                      suffix
                                                      (@List.length.{0} Aeneas.Std.U32
                                                        (@Subtype.val.{1} (List.{0} Aeneas.Std.U32)
                                                          (fun l =>
                                                            @LE.le.{0} Nat instLENat (@List.length.{0} Aeneas.Std.U32 l)
                                                              Aeneas.Std.Usize.max)
                                                          flat))
                                                      (@Subtype.val.{1}
                                                        (List.{0}
                                                          (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                            (Aeneas.Std.Usize.ofNat
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                (instOfNatNat (nat_lit 5)))
                                                              ⋯)))
                                                        (fun l =>
                                                          @LE.le.{0} Nat instLENat
                                                            (@List.length.{0}
                                                              (Aeneas.Std.Array.{0} Aeneas.Std.U32
                                                                (Aeneas.Std.Usize.ofNat
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                    (instOfNatNat (nat_lit 5)))
                                                                  ⋯))
                                                              l)
                                                            Aeneas.Std.Usize.max)
                                                        groups)))
                                                  (NFN_NFB_PhysicalFrame.run (NFN_NFB_GatherFrame.actions rows)
                                                    (NFN_NFB_ReturnedBuffers.initial heap))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (heap
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                    (instOfNatNat (nat_lit 0)))))))))))))))))))))
'NFN_NFB_GeometryComposed.accepted_physical' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```
