import S2W_AuthenticatedInputs

/-! One accepted native owned pair: source cuts, exact ordered outer trace,
success-conditioned oracle and conditional authentication/child geometry.
SourceCuts is an OUTPUT of acceptance inversion, never a premise. This is
not a constructor of the nine-site S2CallerFacts account observation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_NativeConsolidation
open Aeneas Aeneas.Std Result MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_ExtractionBoundary S2W_AuthenticatedInputs

structure FirstCut where
  proofAccount : AdapterRw.Cuts.Account
  publicAccount : AdapterRw.Cuts.Account
  raw : Slice U8
  pub : Slice U8
  statement : AdapterRw.Cuts.Statement
  semantic : AdapterRw.LeadInputs.Public
  proof : Slice U8
  split : Usize

structure SecondCut where
  proofAccount : AdapterRw.Cuts.Account
  checkpointAccount : AdapterRw.Cuts.Account
  raw : Slice U8
  checkpoint : Slice U8
  encoded : Array U8 1880#usize
  proof : Slice U8
  finish : Usize

def SecondCut.pub (s : SecondCut) : Slice U8 := Array.to_slice s.encoded

/-- Only exact source read/dispatch/checked-range facts; all obtained from
accepted source execution by cuts_of_acceptance below. Not trusted. -/
structure SourceCuts (ops : AdapterRw.Ops) (accounts1 accounts2 : Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut) : Prop where
  proof1Index : Slice.index_usize accounts1 0#usize = ok f.proofAccount
  public1Index : Slice.index_usize accounts1 1#usize = ok f.publicAccount
  proof1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.proofAccount = ok (.Ok f.raw)
  public1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.publicAccount = ok (.Ok f.pub)
  decode : ops.op47 f.pub = ok (.Ok f.statement)
  first : AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split = ok (.Ok saved)
  proofLength : (bytesOf f.proof.val).length = 57607
  firstSuffix : bytesOf f.raw.val = (bytesOf f.raw.val).take 688 ++ bytesOf f.proof.val
  proof2Index : Slice.index_usize accounts2 0#usize = ok s.proofAccount
  checkpoint2Index : Slice.index_usize accounts2 6#usize = ok s.checkpointAccount
  proof2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.proofAccount = ok (.Ok s.raw)
  checkpoint2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.checkpointAccount = ok (.Ok s.checkpoint)
  secondRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    s.raw {start := 688#usize, «end» := s.finish} = ok s.proof
  raw2Length : s.raw.val.length = s.finish.val
  second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    s.pub s.proof s.checkpoint () none = ok (.Ok ())
  secondSuffix : bytesOf s.raw.val = (bytesOf s.raw.val).take 688 ++ bytesOf s.proof.val

/-- No source-cut hypotheses: both sets of actual child arguments and both
suffixes are obtained from the two whole accepted native owned calls. -/
theorem cuts_of_acceptance (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : AeneasExtraction ops native1 native2 hashv)
    (program : Program) (accounts1 accounts2 : Accounts) (data1 data2 : Slice U8)
    (slot : Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s, SourceCuts ops accounts1 accounts2 saved f s := by
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ip,iu,rp,ru,dec,first,len,shape⟩ :=
    native_first_fields ops native1 native2 hashv extraction program accounts1 data1 saved accepted1
  rw [extraction.stage2] at accepted2
  obtain ⟨validated,pa2,ca2,raw2,cp2,encoded,proof2,finish,_,ip2,ic2,rp2,rc2,_,range,second,len2⟩ :=
    S2X.second_fixed_range ops program accounts2 data2 slot accepted2
  have shape2 := (AdapterRw.Ranges.suffix_exact raw2 proof2 688#usize finish
    (S2X.successful_range_ordered raw2 proof2 688#usize finish range) len2 range).2
  change raw2.val = raw2.val.take 688 ++ proof2.val at shape2
  have suffix2 : bytesOf raw2.val = (bytesOf raw2.val).take 688 ++ bytesOf proof2.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape2
  exact ⟨⟨pa,pu,raw,pub,statement,semantic,proof,split⟩,
    ⟨pa2,ca2,raw2,cp2,encoded,proof2,finish⟩,
    ⟨ip,iu,rp,ru,dec,first,len,shape,ip2,ic2,rp2,rc2,range,len2,second,suffix2⟩⟩

/-- Consolidate on the witnesses produced above, not independently chosen
caller-site buffers. All extra hypotheses below are individually named
runtime/child boundaries, with no saveCut/sameStoredProof/NativeBinding. -/
theorem accepted_native_consolidation (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : Program) (accounts1 accounts2 : Accounts) (data1 data2 : Slice U8)
    (slot : Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s firstLog finalLog suffix,
      SourceCuts ops accounts1 accounts2 saved f s ∧
      S2W_Trace.run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts1 data1)
        [] = ok (.Ok saved,firstLog) ∧
      S2W_Trace.run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts2 data2 slot)
        firstLog = ok (.Ok (),finalLog) ∧
      S2W_Trace.run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,finalLog) ∧
      finalLog = firstLog ++ suffix ∧
      (∀ e ∈ finalLog, S2W_TraceFacts.ValidEvent ops e) ∧
      CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest ops) () H ∧
      (∀ (decode : HeaderDecode) (y1 : Slice U8) (nodes : Nat → Nat → Slice U8),
        CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split →
        CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint →
        S2W_AuthenticatedInputs.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) →
        S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub →
        S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
        S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
        S2W_ChildJoins.S8StageConeJoin f.proof y1 →
        bytesOf s.proof.val = bytesOf f.proof.val ∧
        bytesOf s.pub.val = bytesOf f.pub.val ∧
        bytesOf s.checkpoint.val = bytesOf saved.val ∧
        (bytesOf saved.val).length = 1768 ∧
        ∃ tr p, OraclePortStoredParserC4.parseReached (bytesOf f.proof.val) tr = some p ∧
          (∀ b k, b < 2 → k < 3 → bytesOf (nodes b k).val =
            slice p.wire (OraclePortSelectedDraft.slotStart (3*b+k))
              (32*OraclePortSelectedDraft.capacity (3*b+k))) ∧
          y1 = S8JoinFrozenScan.segment f.proof 7031 464 ∧
          S8OwnedP6.check_values_owned y1 = ok (.Ok ())) := by
  obtain ⟨f,s,cuts⟩ := cuts_of_acceptance ops native1 native2 hashv extraction program accounts1 accounts2
    data1 data2 slot saved accepted1 accepted2
  obtain ⟨l1,l2,suffix,first,second,both,extension,valid⟩ :=
    accepted_native_observation ops native1 native2 hashv extraction program accounts1 accounts2
      data1 data2 slot saved accepted1 accepted2
  refine ⟨f,s,l1,l2,suffix,cuts,first,second,both,extension,valid,
    native_oracle ops native1 native2 hashv extraction sha256 H p1 runtime,?_⟩
  intro decode y1 nodes writer reader version p2prime entry multiproof scan
  exact authenticated_geometry ops decode H f.semantic f.pub f.proof s.pub s.proof s.checkpoint
    y1 nodes f.split saved cuts.first cuts.second writer reader version p2prime entry multiproof scan

#print axioms cuts_of_acceptance
#print axioms accepted_native_consolidation
#print accepted_native_consolidation
end AspisR1.S2W_NativeConsolidation
end
