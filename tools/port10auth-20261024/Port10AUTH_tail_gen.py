from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port4B_TailRun.lean').read_text().replace('import Port4B_SliceReads','import Port10AUTH_VerifyProjection\nimport Port4B_SliceReads').replace('Port4B_TailRun','Port10AUTH_Tail')
a=s.index('    (binary occupied sibling');b=s.index('    (proof : Slice U8)',a)
s=s[:a]+'''    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (occupied sibling : MultiproofConeP6Callbacks.Parent)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
'''+s[b:]
s=s.replace('(Port3_BatchStd.install (Port4B_VerifyInstall.install base)) D proof root kind hash lo n slot','(Port9OR_BatchStep.ops base) D proof root kind hash lo n slot')
s=s.replace('''      (eval H (MultiproofConeP6Batch.tailState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
        parsed b kind.val nodes s)).2=(true,final)''','''      eval H (MultiproofConeP6Batch.tailState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
        parsed b kind.val nodes s)=
        (CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n n)).1,(true,final))''')
s=s.replace('fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=\n    Port4B_TailReads.reads (Port4B_VerifyInstall.install base) D hash proof root kind lo n slot s.n\n      keys s.idx outIdx s.val outVal run', 'fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead,terminalLogs⟩ :=\n    Port10AUTH_TerminalCut.accepted base D hash proof root kind lo n slot keys s outIdx outVal run')
a=s.index('  obtain ⟨final,verified,indices,values⟩');b=s.index('  have padBytes',a)
s=s[:a]+'''  change (do
    let (accepted,out) ← MultiproofConeRef.reference.verify_owned (Port4B_VerifyInstall.digest D) hash
      root {s with «at»:=0#usize} supplied
    ok (accepted,out.idx,out.val))=ok (true,outIdx,outVal) at verifyRead
  obtain ⟨⟨accepted,final⟩,nativeVerify,output⟩ := Port3_PushFrame.bind_success _ _ _ verifyRead
  have same := Result.ok.inj output
  simp only [Prod.mk.injEq] at same
  obtain ⟨truth,indices,values⟩ := same
  subst accepted
  have codeSuccess := (Port9OR_P6Verify.source D hash root {s with «at»:=0#usize} supplied).trans nativeVerify
  have verified := Port10AUTH_Verify.accepted D hash H oracle
    (MultiproofConeP6Callbacks.nodeWith occupied sibling)
    (MultiproofConeP6Callbacks.node_gate (MultiproofConePhysicalTransport.rawOracle H) occupied sibling occupiedGate siblingGate)
    root {s with «at»:=0#usize} final supplied counted.1 (by rw [suppliedLength];omega)
    (by rw [suppliedLength];have c:=MultiproofConeP6Frozen2Stage.capacity_bound b kind.val hb hk;omega) codeSuccess
  have projectedLogs : (Port9OR_Code.trace D hash (Port9OR_BatchStep.verify root s.idx s.val s.n supplied)).1=
      (Port9OR_Code.trace D hash (Port9OR_P6Verify.code root {s with «at»:=0#usize} supplied)).1 :=
    Port10AUTH_VerifyProjection.log D hash root s supplied
  rw [← projectedLogs,← terminalLogs] at verified
'''+s[b:]
s=s.replace(' :\n    ∃ nodes final,',' :\n    ∃ nodes final,')
s=s.replace('  obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,',
  '  generalize bodyLogEq : CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash\n    (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n n)).1=bodyLog\n  obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,',1)
s=s.replace('  rw [← projectedLogs,← terminalLogs] at verified',
  '  have bodyEquality := (congrArg CheckpointBytes5Inputs.observe (terminalLogs.trans projectedLogs)).symm.trans bodyLogEq\n  have verifiedLog := verified.trans (congrArg (fun log => (log,(true,final))) bodyEquality)')
s=s.replace(' at verified',' at verifiedLog').replace(' using verified',' using verifiedLog')
s=s.replace('/-- Full accepted native terminal transport.', '/-- Full accepted emitted terminal observation transport.')
s=s.replace('Only input provenance and the named P6Boundary remain.', 'Only input provenance, successful-read interpretation and local parent lowerings remain.')
p=L/'Port10AUTH_Tail.lean'
if '--check' in sys.argv: assert p.read_text()==s
else: p.write_text(s)
