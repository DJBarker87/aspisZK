from pathlib import Path
E=Path(__file__).resolve().parent
items=[
 ('Selected','rawSelected','raw00','c.c15 (selectedArray s)','fun _ => raw00 c s'),
 ('ReadonlyProof','raw00','raw01','c.c13 s.proofAccount','fun _ => raw01 c s'),
 ('ReadonlyPublic','raw01','raw02','c.c13 s.publicAccount','fun _ => raw02 c s'),
 ('Checkpoint','raw02','raw03','c.c14 s.checkpointAccount s.program true','fun _ => raw03 c s'),
 ('CheckpointData','raw03','raw04','NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount','fun bytes => raw04 c ⟨s,bytes⟩'),
 ('Zero','raw04','raw05','c.c16 s.checkpointData','fun _ => raw05 c s'),
 ('PublicData','raw05','raw06','NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.publicAccount','fun bytes => raw06 c ⟨s,bytes⟩'),
 ('Decode','raw06','raw07','c.c12 s.publicData','fun statement => raw07 c ⟨s,statement⟩'),
 ('ProofData','raw09','raw10','NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.proofAccount','fun bytes => raw10 c ⟨s,bytes⟩')]
phases=['Selected']*5+['CheckpointData']*2+['PublicData','Candidate']
for (name,before,after,call,next),phase in zip(items,phases):
 deps=['NMT_345StepBase','NMT_345Distinct']
 for raw in [before,after]:deps.append('NMT_345RawSelected'if raw=='rawSelected'else 'NMT_345Raw_'+raw[-2:])
 text=''.join('import '+d+'\n'for d in deps)+'''set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
'''+f'''/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem split{name} {{W : Type}} (c : Calls) (s : {phase} W) :
 {before} c s = tryStep ({call}) ({next}) :=
 emitted_try _ _
#print axioms split{name}
end NMT_345
'''
 (E/('NMT_345Split'+name+'.lean')).write_text(text)
