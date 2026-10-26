# Unchanged actual top statement

Source: lean/Rc8_Top.lean at 418e27640388528f3752de5dade92a450d78d0f8. Source SHA-256 247bc3b1161d1f57cf82ed29f24ff3bce9446e5520d2634d361b01624bc2b173.

Both BEFORE and AFTER are the following identical complete statement. No theorem replacement is proposed.

```lean
theorem deployed {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIo_Install.configuration indexError c reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : F3T_Runtime.Runtime)
    (finishOwners : FGm_Owners.Owners
      (FIo_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIo_Install.select reservation c)) reservation).boundaries)
    (binding : F3T_Runtime.StoredCarrierBinding
      (FIo_Install.configuration indexError c reservation) D
      (F3T_Installed.source (FIo_Install.configuration indexError c reservation) hashv) P runtime)
    :
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIo_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIo_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIo_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (FIo_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (FIo_Install.configuration indexError c reservation).adapter (FIo_Install.configuration indexError c reservation).currentBase (FIo_Install.configuration indexError c reservation).stageBase
        (FIo_Install.configuration indexError c reservation).finish (FIo_Install.configuration indexError c reservation).reserved (FIo_Install.configuration indexError c reservation).query (FIo_Install.configuration indexError c reservation).geometry
        (FIo_Install.configuration indexError c reservation).boundaries (FIo_Install.configuration indexError c reservation).std ∧
    (P2P_Result.Outcome L e1 e2 w1 w2
      (FIo_Install.configuration indexError c reservation).adapter (FIo_Install.configuration indexError c reservation).currentBase
      (FIo_Install.configuration indexError c reservation).reserved (FIo_Install.configuration indexError c reservation).query
      (FIo_Install.configuration indexError c reservation).geometry (FIo_Install.configuration indexError c reservation).stageBase
      (FIo_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIo_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIo_Install.configuration indexError c reservation) hashv P)
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (FIo_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIo_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIo_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (FIo_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIo_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIo_Install.configuration indexError c reservation))
```

Ledger method: use the committed Rc8 flattened obligation recount, retain its row identities, classes and deduplication, then apply the empty source change to the theorem and all definitions in its statement. No row is discharged or renamed by this evidence-only candidate. Distinct actual T83/P18/G13/C0 -> T83/P18/G13/C0; deployment-inclusive T89/P22/G13/C0 -> T89/P22/G13/C0. Delta T0/P0/G0/C0. Premises removed/added/changed: 0/0/0. Quantifiers, carriers, conclusions and failure events are identical.

Non-vacuity: this filtering changes no antecedent and supplies no joint accepted-run witness. Existing conditional non-vacuity results are retained with their existing hypotheses; the joint real-byte fixture remains with JFt_. The matcher comparison and successful importer compiles cannot establish top-level non-vacuity. Target not yet established.

Mechanical inherited-row recount: DFm_ledger-delta.json. Raw actual T83/P19/G13/C0 and combined T89/P23/G13/C0 are also unchanged; L137 is deduplicated against L134 for the distinct counts. No fresh kernel leaf expansion was run.
