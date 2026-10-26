from pathlib import Path
L=Path('lean');s=(L/'Rc5_Result.lean').read_text();s=s.replace('namespace AspisR1.Rc5_Result','namespace AspisR1.Rc6_Result').replace('end AspisR1.Rc5_Result','end AspisR1.Rc6_Result')
s='import Rc5_Result\nimport Rc6_Caller\nimport PFin_Packet\nimport P6C_FullBoundary\n'+s
cfg='(⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError)'
s=s.replace('(prior : Program Bytes State Unit) (events : List S2X.AccountEvent) : Prop :=','(prior : Program Bytes State Unit) (events : List S2X.AccountEvent)\n    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : Prop :=')
marker='      Rc5_Caller.Outcome'
extra='''      PFin_Packet.Facts (bytesOf f.pub.val) (bytesOf f.proof.val) (Tx1Q_Carriers.prepared run.p) H ∧
      P6C_OnCuts.SafeBatches CFG hashv H f s ∧
      P6C_FullBoundary.Facts CFG hashv H saved f s ∧
'''.replace('CFG',cfg)
s=s.replace(marker,extra+'      Rc6_Caller.Outcome')
header=s.split('def Outcome')[0]
args=s.split('def Outcome')[1].split(' : Prop :=')[0].rsplit('    (hashv',1)[0]
# args begins with implicit params and explicit params; use its whole declaration prefix.
baseapp='L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events'
strength='''theorem strengthenARGS
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk CFG) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (source : Rc5_Result.Outcome APP) : Outcome APP hashv := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,caller⟩ := source
  have safe := P6C_OnCuts.same_cuts CFG native1 native2 hashv extraction sha256 H p1 syscall
    e1.first (e2.second secondSizes) saved f s base.1
  have whole := P6C_FullBoundary.same_cuts CFG native1 native2 hashv extraction sha256 H p1 syscall
    e1.first (e2.second secondSizes) saved f s base.1
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
      (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact base.1
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps
      reserved queryOps geoOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  have ⟨cuts,writer,reader,multi,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
  let words := CanonicalCutEnrichedTranscript.wordsFromMaps (fun _=>none) (fun _=>none) (fun _=>none)
  have packet := PFin_Packet.from_cut adapterOps ops reserved queryOps geoOps stageBase finishOps
    (F3M_CircleSource.install B) (NP6_StdModel.calls reservation) e1.first (e2.second secondSizes) saved f s
    pairCuts selected run header1.2.2.1 H native1 native2 hashv pairExtraction sha256 p1 syscall words scanned.2.2
  have joined := Rc6_Caller.from_cut L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B
    (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2
    pairCuts selected header1.2.2.1 scanned.2.2 native1 native2 hashv pairExtraction sha256 p1 syscall caller
  exact ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,packet,safe,whole,joined⟩

#print axioms strengthen
'''.replace('ARGS',args).replace('CFG',cfg).replace('APP',baseapp)
s=s.replace('end AspisR1.Rc6_Result',strength+'end AspisR1.Rc6_Result')
(L/'Rc6_Result.lean').write_text(s)
# reverse transport on precisely the same existential witnesses
forget='''theorem forgetARGS
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (source : Rc6_Result.Outcome APP hashv) : Rc5_Result.Outcome APP := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,packet,safe,whole,caller⟩ := source
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,?_⟩
  intro p2 entry
  exact caller p2

#print axioms forget
'''.replace('ARGS',args).replace('APP',baseapp)
(L/'Rc6_Forget.lean').write_text('import Rc6_Result\n'+header.replace('namespace AspisR1.Rc6_Result','namespace AspisR1.Rc6_Forget')+forget+'end AspisR1.Rc6_Forget\nend\n')
