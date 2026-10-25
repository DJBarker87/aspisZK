from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port10AUTH_FirstOne.lean').read_text();a=s.index('theorem accepted (decoder');b=s.index(' := by\n  let impl',a);stmt=s[a:b]
stmt=stmt.replace('∃ pub proof semantic saved p a g folded,','∃ pub proof semantic saved p a g folded p0 a0 g0 folded0 slice conversion,')
start=stmt.index('      ∀ (parsed :');one=stmt[start:];zero=re.sub(r'\bp\b','p0',one);zero=re.sub(r'\bfolded\b','folded0',zero).replace('q nodes 1\n','q nodes 0\n')
stmt=stmt[:start]+'''      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded0 ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p0 folded0 0#usize hash=ok (.Ok ()) ∧
      (eval H (interpret impl (Port10AUTH_TX1Cut.afterBatch D pub proof 10#usize hash none p0 a0 g0 (.Ok ())))).2=ok (.Ok saved) ∧
      ('''+zero.strip()+''') ∧
      ('''+one.strip()+''')'''
header=s[:s.index('/-- Full first source record')].replace('import Port9OR_FirstBatch','import Port10AUTH_TX1Reached\nimport Port10AUTH_FirstOne').replace('Port10AUTH_FirstOne','Port10AUTH_FirstBoth',1) if False else '''import Port10AUTH_TX1Reached
import Port10AUTH_FirstOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_FirstBoth
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical
'''
proof=''' := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  let input := (Port6AUTH_SourceCut.first rust P H).2.1
  obtain ⟨pub,proof,semantic,saved,p,a,g,folded,hpub,hproof,decoded,tx1,resumed,next,powered,native1,containsOne⟩ :=
    Port10AUTH_FirstOne.accepted decoder adapter ops reserved unwrap rest D hash P H occupied sibling leaf
      occupiedGate siblingGate leafGate sourceAccepted
  obtain ⟨p0,a0,g0,folded0,slice,conversion,earlier,readRoot,arrayRoot,unwrapRoot,native0,suffix,zeroLogs⟩ :=
    Port10AUTH_TX1Reached.accepted ops reserved unwrap rest D hash semantic pub proof saved H tx1
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,p0,a0,g0,folded0,slice,conversion,
    hpub,hproof,decoded,tx1,resumed,next,powered,native1,readRoot,arrayRoot,unwrapRoot,native0,suffix,?_,containsOne⟩
  intro parsed q nodes len wire binding views r0 r1 r2 x read
  have transported := Port10AUTH_Installed.accepted D hash H occupied sibling leaf occupiedGate siblingGate leafGate
    proof len parsed wire p0 folded0 q binding 0#usize (by decide) nodes views r0 r1 r2 native0
  change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes (0#usize).val
    Port4B_BatchJoin.initial)).1 x at read
  rw [transported] at read
  change Port1_Driver.asSlice input.statement.pubBytes=some pub at hpub
  change Port1_Driver.asSlice input.stored=some proof at hproof
  have entry : rust input=Port1_Driver.stages impl D hash semantic pub proof := by
    change Port1_Driver.rust adapter impl D hash input=_
    simp only [Port1_Driver.rust,hpub,hproof,decoded]
  have first := Port7CLEAN_Driver.first_accepted decoder adapter impl D hash P H sourceAccepted
  change (eval H (rust input)).2=true at first
  have stages : (eval H (Port1_Driver.stages impl D hash semantic pub proof)).2=true := by
    rw [entry] at first
    exact first
  obtain ⟨otherSaved,tx1Again,tx2,stageLogs⟩ := Port7CLEAN_Driver.accepted_stages impl D hash semantic pub proof H stages
  have same : otherSaved=saved := core.result.Result.Ok.inj (Result.ok.inj (tx1Again.symm.trans tx1))
  subst otherSaved
  have rustLogs := (congrArg (fun program => (eval H program).1) entry).trans stageLogs
  obtain ⟨before,firstLog⟩ := Port10AUTH_FirstOne.first_logs rust P H
  rw [firstLog,rustLogs,zeroLogs]
  simp only [Read,List.map_append,List.mem_append] at read ⊢
  exact Or.inr (Or.inl (Or.inl (Or.inr read)))

#print axioms accepted
end AspisR1.Port10AUTH_FirstBoth
end
'''
out=header+stmt+proof
audit=R/'tools/port10auth-20261024/final-audit-append.txt'
if audit.exists(): out+='\n'+audit.read_text()
p=L/'Port10AUTH_FirstBoth.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
