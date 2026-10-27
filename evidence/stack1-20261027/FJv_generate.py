"""Archived initial source-port draft, not a regeneration/replay gate.
The final modules include focused, receipt-checked edits and grouped definition
wrappers. Use the committed modules and their exact-source hashes as authority.
"""
from pathlib import Path
import re
p=Path('lean')
# No-finish-law predicate with explicit backward map.
s=(p/'FJv_Finish.lean').read_text();s=s[:s.index('theorem discharge')]
s=s.replace('namespace AspisR1.FJv_Finish','namespace AspisR1.FJv_DFinish').replace('import FJu_Finish','import FJv_Finish')
a=s.index('    ∀ (semantic_S3_S9');b=s.index('    Collision H',a);s=s[:a]+s[b:]
t=(p/'FJv_Finish.lean').read_text();t=t[t.index('theorem discharge'):t.index('#print axioms discharge')]
t=t.replace('FJu_Finish.Outcome','FJv_Finish.Outcome')
a=t.index('    (pair :');b=t.index(' :\n    Outcome',a)
t=t[:a]+'''    (terminal : FJu_Remaining.Endpoint i.decoded
      (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i.data)'''+t[b:]
t=t.replace('rest pair⟩','rest terminal⟩').replace('intro _ semanticLaw\n  exact rest semanticLaw','intro _\n  exact rest')
s+=t+'#print axioms discharge\n#print axioms forget\nend AspisR1.FJv_DFinish\nend\n';(p/'FJv_DFinish.lean').write_text(s)
# Every new D wrapper is a literal port of FJt with a changed leaf.
names=['Literal','PairCont','PairCaller','PairResult','NativePair','Cont','Caller','FinalResult','FinalSource','R5Result','R5Close','R6Caller','R6Result','BoundCaller','Result','Release','NativeAccepted']
mp={'FJt_'+n:'FJv_D'+n for n in names};mp['FJt_NativeFinish']='FJv_DFinish'
for n in names:
 s=(p/('FJt_'+n+'.lean')).read_text()
 for old,new in mp.items():s=s.replace(old,new)
 (p/('FJv_D'+n+'.lean')).write_text(s)
# Specialise only constructors where simultaneous derivation needs installed pair/query/geometry.
f=p/'FJv_DLiteral.lean';s=f.read_text();a=s.index('theorem from_cut');prefix=s[:a];t=s[a:]
t=t.replace('theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)\n    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)\n    (stage : VTop_Stages.Ops) {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)', '''theorem from_cut {CoreError : Type} (missing : IDa_Deployed.Uninstalled CoreError)
    (err : CoreError) (r : NP6_StdModel.Reservation)''')
# Remove supplied finishSeed/installed/positions: fixed by exact configuration.
a=t.index('    (finishSeed :');b=t.index('    (sameSaved :',a);t=t[:a]+t[b:]
a=t.index('    (sameSaved :');b=t.index(' :\n    Outcome',a)
t=t[:b]+'''\n    (authentication : ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
      (rho : OraclePortCheckpointAbiC5.K) (q : Fin 22 → Fin 262144),
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
      AuS1_Finish.Collision H trace authParsed q ∨
      ∃ recovered : Nat → Option Bytes,∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload authParsed 2 pos))'''+t[b:]
# Locally define the fixed projections by let binders in theorem? replace every token with qualified configuration field.
c='(FJt_GlobalTerminal.configuration missing err r)'
for key,field in [('adapter','adapter'),('ops','currentBase'),('reserved','reserved'),('query','query'),('geo','geometry'),('stage','stageBase'),('finish','finish')]:
 t=re.sub(r'\b'+key+r'\b', c+'.'+field,t)
# FIs_OnRun install args replace removed names.
t=t.replace(' finishSeed ',f' {c}.finish ').replace('positions.1 rfl rfl positions.2.1 positions.2.2 installed','rfl rfl rfl rfl rfl rfl')
# Common parser equality before assembling outer result.
a=t.index('  have current :')
t=t[:a]+'''  have parserPhysical := parser
  rw [stored] at parserPhysical
  have parsedSame : parsed=authParsed := Option.some.inj
    ((OraclePortStoredParserC4.parsed _ _ _ parserPhysical).1.symm.trans sourceParsed)
  subst authParsed
'''+t[a:]
a=t.index('    apply FJv_DFinish.strengthen')
t=t[:a]+'''    let c := FJt_GlobalTerminal.configuration missing err r
    let base := IDa_Deployed.deployedConfiguration missing err r
    have cutsSdk : S2W_NativeConsolidation.SourceCuts (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install c.adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base c.stageBase)
          c.reserved c.query c.geometry)) c.finish)
        (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
        (F3M_CircleSource.install (FIq_Install.boundaries seed)) std) accounts1 accounts2 saved f s := by
      rw [AuS1_Install.dictionary]
      exact cuts
    obtain ⟨actual,actualCalls,aux⟩ := FJp_ConsSecond.accepted c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std
      accounts1 accounts2 saved f s cutsSdk
    have sizeProof : f.proof.val.length=57607 := by
      simpa only [bytesOf,List.length_map] using cuts.proofLength
    have auth := authentication _ _ q prepare
    have matching : AuS1_Finish.Collision H trace parsed q ∨ ∀ j,MatchingSupport.match0 i.data (q j) := by
      rcases auth with hit | ⟨recovered,authenticated⟩
      · exact Or.inl hit
      · right
        exact FJp_NativePair.value err base r (Op5T_Concrete.current c.currentBase)
          (F3M_CircleSource.install (FIq_Install.boundaries seed)) std _ ()
          (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
          s.checkpoint s.proof s.pub actual aux actualCalls.2 sameSaved sameProof.symm sizeProof
          out parsed view q _ i same equal prepare read queries
          (OraclePortCompactDraft.parse_header _ _ sourceParsed).2 recovered authenticated
    have matched := FJp_Finish.strengthen (old:=onRun) matching
    have chained := FJu_Finish.strengthen (old:=matched) (by
      intro terminal selectedView claim polys opened claimRead polyRead
      rw [wire] at opened
      have first := FIr_PhysicalInitial.on_run (Op5T_Concrete.current c.currentBase)
        c.reserved c.query c.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std _ ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
        parsed q _ parserPhysical selectedView claim polys opened claimRead polyRead
      have sameView := Option.some.inj (opening.symm.trans opened)
      subst selectedView
      have chain := FIr_PhysicalChain.on_run (Op5T_Concrete.current c.currentBase)
        c.reserved c.query c.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) std _ ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
        parsed q _ parserPhysical view claim polys opened claimRead polyRead out same equal
        (fun j=>FIr_TranscriptRange.view H model.proof model.semantic.value parsed q view opened (15+j.val))
      exact ⟨first,chain,terminal view claim polys (by rw [wire];exact opened) claimRead polyRead⟩)
    have range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0) := by
      intro j
      exact FIr_TranscriptRange.view H model.proof model.semantic.value parsed q view opening _
    have pairLaw := FJs_OnRun.law r base.finish s.proof tx2 _ enriched.2.2 rfl rfl
      parsed q _ i view parsedNative read opening _ savedFields.1 range
    have paired := FJv_Finish.discharge (old:=chained) pairLaw
    apply FJv_DFinish.discharge (old:=paired)
    rw [wire]
    exact endpoint
#print axioms from_cut
end AspisR1.FJv_DLiteral
end
'''
prefix='import FJv_Finish\nimport FJt_GlobalTerminal\nimport FJp_ConsSecond\nimport FJp_NativePair\nimport FJu_NativeLiteral\nimport FJs_OnRun\n'+prefix
f.write_text(prefix+t)
# NativePair choose FJp retained root source. Restrict theorem to exact config, generic definition remains.
f=p/'FJv_DNativePair.lean';s=f.read_text();a=s.index('theorem accepted');prefix=s[:a];t=s[a:]
a=t.index('    (adapterOps :');b=t.index('    (seed :',a)
t=t[:a]+'''    (missing : IDa_Deployed.Uninstalled CoreError) (err : CoreError) (r : NP6_StdModel.Reservation)
'''+t[b:]
# remove implicit F universe parameter to avoid inference ambiguity
# retain F in implicit list only used finishSeed; replace that by FIo_Install.W
t=t.replace(' M Cv F CoreError',' M Cv CoreError').replace('FinishOps F)','FinishOps FIo_Install.W)')
a=t.index('    (finishSeed :');b=t.index(' :\n    FJv_DPairResult',a);t=t[:a]+t[b:]
c='(FJt_GlobalTerminal.configuration missing err r)'
for key,field in [('adapterOps','adapter'),('ops','currentBase'),('reserved','reserved'),('queryOps','query'),('geoOps','geometry'),('stageBase','stageBase'),('finishOps','finish')]:t=re.sub(r'\b'+key+r'\b',c+'.'+field,t)
t=t.replace('FIs_P2P_PairSelected.accepted','FJp_Ret_PairSelected.accepted').replace('run,tx2,origin,calls,base','run,rootBinding,tx2,origin,calls,base')
# inserted rootBinding only obtain, not refine target
needle='  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2';t=t.replace(needle,'  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2')
# authentication on same source parsed prefix trace.
a=t.index('  refine ⟨authParsed,frame,parser,frameRead,target,?_⟩')
t=t[:a]+'''  obtain ⟨rootView,rootRange,rootCopy⟩ := rootBinding
  obtain ⟨newFrame,newRead,newTarget,auth⟩ := AuS1_OnRun.same_pair prior
    '''+c+'''.adapter '''+c+'''.currentBase '''+c+'''.stageBase '''+c+'''.finish
    '''+c+'''.reserved '''+c+'''.query '''+c+'''.geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) claimsStd
    native1 native2 hashv pairExtraction sha256 H p1 syscall e1.first (e2.second secondSizes)
    saved f s pairCuts sameCheckpoint sameProof authParsed parser run rootView rootRange rootCopy
'''+t[a:]
a=t.index('  exact FJv_DLiteral.from_cut');t=t[:a]+'''  refine FJv_DLiteral.from_cut missing err r seed claimsStd
    e1.first (e2.second secondSizes) saved f s pairCuts selected run header1.2.2.1 H
    native1 native2 hashv pairExtraction sha256 p1 syscall words scanned.2.2 _ authParsed parser
    sameProof.symm tx2 ten finish queryLeaves geoLeaves domain multiply one inverse _ () calls
    sameCheckpoint ?_
  intro data rho q prepared
  rcases auth data rho q prepared with hit | indexed
  · exact Or.inl hit
  · exact Or.inr ⟨OraclePortAllSelectedRecoveryC6.recovered _ newFrame authParsed 2,indexed⟩
#print axioms accepted
end AspisR1.FJv_DNativePair
end
'''
f.write_text('import FJp_RetPrefix\nimport FJt_GlobalTerminal\n'+prefix+t)
f=p/'FJv_DFinalSource.lean';s=f.read_text();s=s.replace('      c.adapter c.currentBase c.reserved c.query c.geometry c.stageBase c.finish (IDa_Deployed.boundaries reservation)', '      missing indexError reservation (IDa_Deployed.boundaries reservation)');s=s.replace('Par_Parameters.deployed root length words\n      c.finish installed ⟨rfl,rfl,rfl⟩','Par_Parameters.deployed root length words');f.write_text(s)
