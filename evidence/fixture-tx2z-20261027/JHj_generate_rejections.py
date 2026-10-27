from pathlib import Path
R=Path(__file__).resolve().parents[2]
for name,slot,seeds,closure in [
 ('MasterPda',None,'s2','closure'),('CheckpointPda',None,'s6','closure_1'),('LanePda',None,'s10','closure_2')]:
 src=(R/'lean'/('JHj_'+name+'.lean')).read_text();args=src[src.index('def run')+7:src.index(' :\n    Result (core.result.Result')]
 # Same generic parameters as the actual continuation.
 argnames=['ops','verifier_program','pool_program','output_lane','current_slot','master_account','checkpoint_account','lane_account','registry_account','entry_account','val1','p']
 argnames += {'MasterPda':['s2'],'CheckpointPda':['val4','s6'],'LanePda':['val4','p2','val7','s10']}[name]
 for kind,typ,call,result in [('Error','solana_pubkey.PubkeyError','ok (.Err error)','ok (.Err solana_program_error.ProgramError.InvalidAccountData)'),('Failure','Aeneas.Std.Error','.fail error','.fail error'),('Divergence',None,'.div','.div')]:
  outname='JHj_'+name+kind
  s='import JHj_'+name+'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+outname+'\nopen Aeneas Aeneas.Std Result\nopen _root_.AdapterRw\n\n'
  s+='theorem source '+args+ ('\n    (error : '+typ+')' if typ else '')+'\n    (rejected : ops.op38 '+seeds+' pool_program='+call+') :\n    JHj_'+name+'.run '+' '.join(argnames)+'=\n    '+result+' := by\n  unfold JHj_'+name+'.run\n  rw [rejected]\n  rfl\n#print axioms source\nend AspisR1.'+outname+'\nend\n'
  (R/'lean'/(outname+'.lean')).write_text(s)
