from pathlib import Path
R=Path(__file__).resolve().parents[2]
common='''set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value
'''
args='(JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot\n      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)\n      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key'
ca=' (e2.snapshot 2 192 192).key'
cp=' JHg_AccountValues.checkpoint'
la=' JHg_AccountValues.lane'
def call(n,extra=''):return 'JHj_'+n+'.run '+args+extra
def write(n,imports,prem,lhs,rhs,proof):
 name='JHj_'+n
 s=''.join('import '+x+'\n' for x in imports+['JHj_Seeds','JHd_ReferenceSlots'])
 s+=common.format(name=name)+'\n/-- Caller-stage computation. Native child observations remain explicit. -/\ntheorem source (base : Ops) (slot : U64)'+prem+' :\n    '+lhs+'=\n    '+rhs+' := by\n'+proof+'\n#print axioms source\nend AspisR1.'+name+'\nend\n'
 (R/'lean'/(name+'.lean')).write_text(s)
write('MasterPdaStep',['JHj_MasterPda','JHj_MasterRegistry','JHj_KeyComparison'],
 '\n    (pda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.master JHb_Programs.pool=ok (.Ok JHj_Seeds.key))',
 call('MasterPda',' JHj_Seeds.master'),call('MasterRegistry'),
 '''  unfold JHj_MasterPda.run
  rw [pda,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHj_KeyComparison.different,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rfl''')
registry='r1_pool_adapter.owned.authenticate_invariant_release_registry (JHd_ReferenceSlots.install base)\n      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master\n      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot'
write('MasterRegistryStep',['JHj_MasterRegistry','JHj_CheckpointRead'],
 '\n    (registry : '+registry+'=ok (.Ok ()))',call('MasterRegistry'),call('CheckpointRead'),
 '''  unfold JHj_MasterRegistry.run
  rw [registry,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl''')
write('CheckpointReadStep',['JHj_CheckpointRead','JHj_CheckpointDecoded','JHi_AccountReads'],
 '\n    (decoded : (JHd_ReferenceSlots.install base).op49 JHg_DataForest.value=ok (.Ok JHg_AccountValues.checkpoint))',
 call('CheckpointRead'),call('CheckpointDecoded',cp),
 '''  unfold JHj_CheckpointRead.run
  rw [JHi_AccountReads.forest,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [decoded,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl''')
write('CheckpointPrefix',['JHj_CheckpointDecoded','JHj_CheckpointPda','JHj_CheckpointGuards'],
 '',call('CheckpointDecoded',cp),call('CheckpointPda',cp+' JHj_Seeds.checkpoint'),
 '''  unfold JHj_CheckpointDecoded.run
  change (ok JHj_Seeds.key >>= _) = _
  rw [bind_tc_ok,JHj_CheckpointGuards.master,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_CheckpointGuards.domain,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  unfold JHj_CheckpointPda.run JHj_Seeds.checkpoint
  simp only [JHd_ReferenceSlots.install,JHd_KeyStd.install,JGx_MagicStd.install,
    JHd_ReferenceSlots.leaves,lift,bind_tc_ok]
  rfl''')
write('CheckpointPdaStep',['JHj_CheckpointPda','JHj_LaneRead','JHj_KeyComparison'],
 '\n    (pda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.checkpoint JHb_Programs.pool=ok (.Ok (e2.snapshot 2 192 192).key))',
 call('CheckpointPda',cp+' JHj_Seeds.checkpoint'),call('LaneRead',cp+ca),
 '''  unfold JHj_CheckpointPda.run
  rw [pda,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    r1_pool_adapter.owned.OwnedAccount.impl.key]
  rw [JHj_KeyComparison.different,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rfl''')
write('LaneReadStep',['JHj_LaneRead','JHj_LaneDecoded','JHi_AccountReads'],
 '\n    (decoded : (JHd_ReferenceSlots.install base).op50 JHb_DataLane.value=ok (.Ok JHg_AccountValues.lane))',
 call('LaneRead',cp+ca),call('LaneDecoded',cp+ca+la),
 '''  unfold JHj_LaneRead.run
  rw [JHi_AccountReads.lane,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [decoded,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl''')
write('LanePrefix',['JHj_LaneDecoded','JHj_LanePda','JHj_LaneGuards'],
 '',call('LaneDecoded',cp+ca+la),call('LanePda',cp+ca+la+' JHj_Seeds.lane'),
 '''  unfold JHj_LaneDecoded.run
  change (ok JHj_Seeds.key >>= _) = _
  rw [bind_tc_ok,JHj_LaneGuards.master,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_LaneGuards.lane]
  simp only [Bool.false_eq_true,if_false]
  unfold JHj_LanePda.run JHj_Seeds.lane
  simp only [JHd_ReferenceSlots.install,JHd_KeyStd.install,JGx_MagicStd.install,
    JHd_ReferenceSlots.leaves,lift,bind_tc_ok]
  rfl''')
write('LanePdaStep',['JHj_LanePda','JHj_KeyComparison'],
 '\n    (pda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.lane JHb_Programs.pool=ok (.Ok (e2.snapshot 3 768 768).key))',
 call('LanePda',cp+ca+la+' JHj_Seeds.lane'),'ok (.Ok JHg_AccountValues.value)',
 '''  unfold JHj_LanePda.run
  rw [pda,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    r1_pool_adapter.owned.OwnedAccount.impl.key]
  rw [JHj_KeyComparison.different,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  change ok (.Ok _) = ok (.Ok JHg_AccountValues.value)
  rfl''')
