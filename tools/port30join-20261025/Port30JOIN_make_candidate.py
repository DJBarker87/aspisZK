"""Construct a reviewable concrete theorem from pinned complete statement spans.
Text construction only: no elaboration, kernel call, or project trust import.
"""
from pathlib import Path
D=Path('evidence/port30join-20261025/sources')
s1=(D/'d346dc7cb7-S1SdkSelectedSemanticTraceV1.lean.txt').read_text()
s2=(D/'904745b496-S2W_D189Consolidation.lean.txt').read_text()
I='''(AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))'''
head=s1[s1.index('theorem original_sdk_selected_semantic_trace'):s1.index(' :\n    post =')]
head=head.replace('original_sdk_selected_semantic_trace {W A M Cv : Type}', 'accepted_original_sdk_s2_s1 {W A E M Cv : Type}')
head=head.replace('(e : Entry) (world : W)', '(e : Entry) (e2 : Entry) (world world2 : W)')
head=head.replace('(adapterOps : AdapterRw.Ops)', '''(admission2 : S2W_D189Consolidation.RuntimeEntrypointAdmission L e2 world2 7)
    (adapterOps : AdapterRw.Ops)''')
head=head.replace('(program : AdapterRw.solana_pubkey.Pubkey)', '''(sha256 H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : AdapterRw.solana_pubkey.Pubkey)''')
head += '''
    (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state2 final2 : A) (post2 : Heap (Nat → Record))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (port : S2W_ExpandedChildren.ChildConeJoin E '''+I+''')
    (firstMarks : S2W_TraceSplice.FirstMarks port)
    (secondMarks : S2W_TraceSplice.SecondMarks port)'''
# Preserve complete SDK codec/reuse conclusion as well as full S1 numeric trace.
sdk=(D/'d346dc7cb7-S6SdkSelectedSemanticCallerV1.lean.txt').read_text()
codec=sdk[sdk.index('      ∃ encoded,'):sdk.index(' := by')].replace(' saved',' out')
numeric=s1[s1.index('      f.pub ='):s1.index(' := by')]
s2con=s2[s2.index('      S2W_ExpandedTrace.runExpanded'):s2.index(' := by\n  obtain ⟨owned1')]
s2con=s2con.replace(' ops', ' '+I).replace('e1','e').replace('w1','world').replace('w2','world2').replace('saved','out').replace('post1','post')
s2con=s2con.replace('data1','data')
V='(NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)'
codec=codec.replace('decode f.pub', 'AspisS6CurrentCodecInstallation.decode f.pub')
codec=codec.replace('toPoolV1PairForestTerminalStatementV1 f.statement','AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement')
codec=codec.replace('(install ops vops)',I).replace('vops',V)
codec=codec.replace('(toDigest ', '(AspisS6CurrentFirstInstallation.toDigest ').replace('(fromError error)', '(AspisS6CurrentVerifierCarrier.fromError error)').replace('ops.op44', 'adapterOps.op44')
# f is the selected cut in the final continuation; rawCut is explicit provenance.
con=''' :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes out)) ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    ∃ (rawCut f : FirstCut) (s : SecondCut) selectedPublic outer pre middle fs ss,
      SourceCuts '''+I+''' e.first (e2.second secondSizes) out rawCut s ∧
      f = {rawCut with semantic := selectedPublic} ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        rawCut.statement = ok selectedPublic ∧
      SourceCuts '''+I+''' e.first (e2.second secondSizes) out f s ∧
      ('''+codec.strip()+''') ∧
      ('''+numeric.strip()+''') ∧
'''+s2con
proof=''' := by
  let installed := '''+I+'''
  have wrapped : S2W_D189Wrappers.first native1 copy allocator e program data initial =
      ok (.Ok (out,post,final)) := by
    rw [AspisS6SdkFirstObjectEquivalence.first_eq_original]
    exact accepted
  obtain ⟨rawCut,s,outer,pre,middle,fs,ss,cuts,expanded,ownedFrame,layout,
      unchanged,frame1,frame2,_oldConditional⟩ :=
    S2W_D189Consolidation.accepted_run L sdk copy std allocator e e2 world world2
      admission admission2 installed native1 native2 hashv extraction sha256 H p1 syscall
      program data data2 slot initial state2 final final2 out post post2 wrapped accepted2
      port firstMarks secondMarks
  obtain ⟨written,frame,allS1⟩ :=
    AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace
      L sdk copy std allocator e world admission adapterOps ops B native1 native2 hashv extraction
      p root length program data out initial final post accepted
  obtain ⟨selectedPublic,selection,chosen,numeric⟩ :=
    allS1 (e2.second secondSizes) rawCut s cuts
  let f : FirstCut := {rawCut with semantic := selectedPublic}
  obtain ⟨_,_,allSdk⟩ := AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts
    L sdk copy std allocator e world admission adapterOps
    (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    native1 native2 hashv extraction program data initial final out post accepted
  obtain ⟨_,_,_,_,_,_,codec⟩ := allSdk (e2.second secondSizes) f s chosen
  refine ⟨written,frame,rawCut,f,s,selectedPublic,outer,pre,middle,fs,ss,
    cuts,rfl,selection,chosen,codec,numeric,expanded,ownedFrame,layout,
    unchanged,frame1,frame2,?_⟩
  intro decode nodes y1 writer reader history p2prime entry multiproof scan
  obtain ⟨owned1,_⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final out post wrapped
  have source1 := (extraction.stage1 program e.first data).symm.trans owned1
  have destinationSize := S2W_D189Entry.checkpoint_size e installed program data out source1
  have versionAtWrite : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket e.heap 2 0 0 (source (nativeBytes out))).payload
        (e.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) := by
    rw [← written]; exact history
  obtain ⟨_,⟨version⟩⟩ := returned_committed e.heap 2 0 0 out (bytesOf s.checkpoint.val)
    rfl rfl destinationSize (writer.size out chosen.first) versionAtWrite
  obtain ⟨parsed,partialFacts⟩ := S2W_InputSchedule.input_schedule installed H
    e.first (e2.second secondSizes) f s out chosen decode nodes y1
    writer reader version p2prime entry multiproof scan
    (S2W_DigestExtraction.native_oracle installed native1 native2 hashv extraction sha256 H p1 syscall)
    pre middle fs ss (S2W_D189Consolidation.before e e2) (S2W_D189Consolidation.after e e2 post)
  have frames := S2W_D189Consolidation.wrapper_frames e e2 installed program data out source1 post written
  refine ⟨parsed,?_,?_⟩
  · apply (S2W_TwoFieldAudit.full_fields_iff _ installed H _ _ _ parsed partialFacts).2
    exact ⟨fun site _ a allowed => frames.1 site a allowed,fun _ => frames.2⟩
  · intro site
    rw [layout]
    rfl

#print axioms accepted_original_sdk_s2_s1
end Port30JOIN
end
'''
opens=s1[s1.index('open Aeneas'):s1.index('/-- Complete')].replace('namespace AspisS1SdkSelectedSemanticTrace','namespace Port30JOIN')
opens+='open AspisR1.S2W_D189Consolidation AspisR1.S2W_AuthenticatedInputs\nopen AspisR1.S2W_InputSchedule AspisR1.S2W_ExpandedChildren AspisR1.S2W_TraceSplice\nopen AspisR1.MultiproofConeCanonical\n'
Path('tools/port30join-20261025/Port30JOIN_Composed.lean').write_text('''/- UNCOMPILED CANDIDATE. Requires a reviewed, kernel-reconstructed closure.
No direct project trust imports. This file has not been elaborated. -/
import Port30JOIN_CheckedClosure
set_option autoImplicit false
noncomputable section
'''+opens+head+con+proof)
print('wrote concrete statement and proof candidate; uncompiled')
