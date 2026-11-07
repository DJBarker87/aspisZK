"""Generate only source-order single-call erasure equations; never row credit.
Inputs: retained literal source program; exact child/primitive owners in table.
The compiler checks each equation before its dependent fold may consume it.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
s=(E/'NMX_SourceProgram.lean').read_text().split(' else\n',1)[1].split('\nend NMX_SourceProgram')[0]
blocks=[]
for line in s.splitlines():
 if line.startswith('  ') and not line.startswith('   '):blocks.append(line[2:])
 elif blocks:blocks[-1]+='\n'+line[2:]
types={
'ops':'Ops','verifier':'solana_pubkey.Pubkey','accounts':'Slice r1_pool_adapter.owned.OwnedAccount',
'pool':'solana_pubkey.Pubkey','outputLane':'U8','slot':'U64',
**{n:'r1_pool_adapter.owned.OwnedAccount' for n in ['proof','masterAccount','checkpointAccount','laneAccount','registryAccount','entryAccount','verifierCheckpoint']},
**{n:'Slice U8' for n in ['masterBytes','checkpointBytes','laneBytes','mintSeed','bumpSeed','checkpointMasterSeed','sequenceSeed','checkpointBump','laneMasterSeed','laneIdSeed','laneBump']},
**{n:'Slice (Slice U8)' for n in ['masterSeeds','checkpointSeeds','laneSeeds']},
**{n:'solana_pubkey.Pubkey' for n in ['masterKey','mintKey','derivedMaster','derivedCheckpoint','checkpointKey','derivedLane','laneKey']},
**{n:'Array U8 32#usize' for n in ['masterKeyBytes','checkpointMasterBytes','laneMasterBytes','snapshotPool','returnedMasterBytes','returnedCheckpointBytes','returnedLaneBytes']},
**{n:'Bool' for n in ['wrongMaster','wrongMasterPda','wrongCheckpointMaster','wrongDeployment','wrongCheckpointPda','wrongLaneMaster','wrongLanePda']},
'allLanes':'U8','master':'Box Master','checkpoint':'Box Checkpoint','lane':'Box Lane','live':'Box Snapshot'}
commands={
'readonlyBuffer':('Unit','r1_pool_adapter.owned.require_readonly_buffer {a}','rust'),
'checkpointGuard':('Unit','r1_pool_adapter.owned.require_verifier_checkpoint ops {a}','rust'),
'readonlyAccount':('Unit','r1_pool_adapter.owned.require_readonly_account ops {a}','rust'),
'distinct':('Unit','r1_pool_adapter.owned.require_distinct_accounts ops {a}','rust'),
'data':('Slice U8','r1_pool_adapter.owned.OwnedAccount.data ops {a}','rust'),
'key':('solana_pubkey.Pubkey','r1_pool_adapter.owned.OwnedAccount.impl.key {a}','raw'),
 'toBytes':('Array U8 32#usize','ops.op39 {a}','raw'),
 'fromBytes':('solana_pubkey.Pubkey','ops.op37 {a}','raw'),
 'asRef':('Slice U8','ops.op40 {a}','raw'),
 'master':('Box Master','ops.op48 {a}','box_master'),
 'checkpoint':('Box Checkpoint','ops.op49 {a}','box_checkpoint'),
 'lane':('Box Lane','ops.op50 {a}','box_lane'),
 'pda':('solana_pubkey.Pubkey','unused','pda'),
 'registry':('Unit','r1_pool_adapter.owned.authenticate_invariant_release_registry ops {a}','rust'),
 'snapshot':('Box Snapshot','unused','snapshot')}
manifest=[]
for block in blocks:
 m=re.match(r'let (\w+) ← (.*)',block,re.S)
 if m:var,term=m.groups();A=types[var]
 elif block.startswith(('call ','check ')):term=block;A='Unit'
 else:continue
 num=len(manifest)+1;mod=f'NMX_S{num:03d}'
 if term.startswith('raw '):kind='raw';rhs=term[4:];proof='exact NMX_ResultSteps.raw ops owners _ next';out=f'({rhs}) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())'
 elif term.startswith('check '):kind='check';cond=term[6:];out=f'if {cond} then ok (.Err .InvalidAccountData) else NMX_ValueLink.erase (eval (source ops owners) (next ()) ())';proof=f'cases h : ({cond}) <;> simp [NMX_SourceProgram.check,h,NMX_Program.bind,eval,NMX_ValueLink.erase]'
 else:
  mt=re.fullmatch(r'call \(\.(\w+) (.*)\)',term,re.S);assert mt,term
  cmd,args=mt.groups();A2,r,kind=commands[cmd];assert A==A2,(A,A2,term)
  r=r.format(a=args)
  k='fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())'
  if kind=='rust':out=f'tryThen ({r}) ({k})';proof='rw [NMX_StepCore.entered]\n exact NMX_ResultSteps.rust ops owners _ _ next'
  elif kind=='raw':
   out=f'({r}) >>= {k}';proof='rw [NMX_StepCore.entered]\n simp only [source]\n rw [NMX_ErasureLaws.continue_raw]\n cases '+f'h : {r}'+' <;> rfl'
  elif kind.startswith('box_'):
   owner=kind[4:];out=f'tryThen ({r}) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.{owner},value⟩) ()))';proof='rw [NMX_StepCore.entered]\n exact NMX_ResultSteps.boxed ops owners _ _ _ next'
  elif kind=='pda':
   # Keep the actual mapped reply folded, including all PubkeyError payload arms.
   arg= args.split();assert len(arg)==2
   r=f'(do let reply ← ops.op38 {args}; match reply with | .Ok key => ok (.Ok key) | .Err _ => ok (.Err .InvalidAccountData))'
   out=f'tryThen {r} ({k})';proof='rw [NMX_StepCore.entered]\n exact NMX_ResultSteps.rust ops owners _ _ next'
  else:
   out='NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.snapshot,'+args+'⟩) ())'
   proof='rw [NMX_StepCore.entered]\n exact NMX_ValueLink.erase_prepend [] _'
 used=[n for n in types if n!='ops' and re.search(r'\b'+n+r'\b',term)]
 params='\n '.join(f'({n} : {types[n]})' for n in used)
 text=f'''import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace {mod}
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence {num}: {kind}; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) {params}
 (next : {A} → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.{term}) next) ()) =
 {out} := by
 {proof}
#print axioms step
end {mod}
end
'''
 # Only qualify the outer call/raw/check, not already-qualified nested names.
 (E/(mod+'.lean')).write_text(text)
 manifest.append(dict(occurrence=num,module=mod,source=term,kind=kind,parameters=used))
(E/'NMX_STEP_MANIFEST.json').write_text(json.dumps(manifest,indent=1)+'\n')
print(len(manifest))
