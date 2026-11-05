from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NIN_PhysicalInstance.lean').read_text()
header=s[:s.index('/-- Universal')].replace('import NIN_Cuts','import NIN_PhysicalInstance\nimport NIN_WriterProducer').replace('AspisR1.NIN_PhysicalInstance','AspisR1.NIN_NativeInstance')
header=header.replace('(base : DrvC_Installation.Configuration FIo_Install.W C) (err : C)','(missing : IDa_Deployed.Uninstalled C) (err : C)')
header=header.replace('FIp_Install.configuration err base r','NHW_DeployedQuery.configuration missing err r')
sig=s[s.index('theorem physical_instance'):s.index(' :\n    (NGP_L159.L159_statement')].replace('theorem physical_instance','theorem from_native')
sig=sig.replace('    (prepared : CheckpointBytes5Writer.Prepared) (accumulator : CheckpointBytes5Writer.Accumulator)\n    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)\n    (hp hu hc : CheckpointBytes5Effect.Digest)\n','')
sig=sig.replace('(final1 : A) (post1 : Heap (Nat → Record))','''(final1 : A) (post1 : Heap (Nat → Record)) (saved : alloc.vec.Vec U8)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk cfg) n1 n2 hashv)''')
sig=sig.replace('(NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)','saved')
conclusion=''' :
    (NGP_L159.L159_statement p t u
      {proof1 := f.proof,public1 := f.pub,proof2 := s.proof,public2 := s.pub,
       checkpointRead := s.checkpoint,
       saved := saved,emittedStatement := emittedStatement,poolRead := authenticated}
      Q (eval H (Hiq_RecordedJoint.program source ARQ_Observer.project
        (ARQ_Observer.select cfg id)))) ∧
    verifierEntry poolInvocation = CPG_Projection.entry p u := by
  obtain ⟨prepared,accumulator,domain,hp,hu,hc,same,writer⟩ :=
    NIN_WriterProducer.from_native missing err r n1 n2 hashv extraction copy std allocator
      ((eval H source).2).1.entry id ((eval H source).2).1.data ((eval H source).2).1.state
      final1 saved post1 native_writer_result
  subst saved
  exact NIN_PhysicalInstance.physical_instance
    (IDa_Deployed.deployedConfiguration missing err r) err r hashv copy allocator a H
    Q bound reached prepared accumulator domain hp hu hc p t u n1 n2 actions std valid1
    system final1 post1 game writer protection ordinary RuntimePersistence L sdk w2 related2 valid2
    f s finish1 proof1Index public1Index proof1Read public1Read range1 length1
    proof2Index proof2Read range2 length2 v validation encoding writerResult
    checkpoint2Index checkpoint2Read readerResult runtime law emitInvocation poolInvocation
    context program selected readState state after emittedStatement sameCpi selectedProgram
    noInterveningCpi emitted authenticated events acceptedDecoder validate lane image checked advanced
    verifierEntry sameVerifierEntry
#print axioms from_native
end
end AspisR1.NIN_NativeInstance
end
'''
(E/'NIN_NativeInstance.lean').write_text(header+'''/-- Derive all writer witnesses from the actual accepted wrapper with retained
extraction; do not require a caller-selected KNE state or writer-result identity.
Physical cut/exporter/Pool associations remain the original exact hypotheses. -/
'''+sig+conclusion)
