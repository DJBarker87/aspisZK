from pathlib import Path
p=Path(__file__).resolve().parent
header='set_option autoImplicit false\nnamespace NMT_R2_345\nopen RSL NMT_345Observation NMT_R2_Observation\n'
for name,frame,expr in [
 ('Distinct','Parent','requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount]'),
 ('ReadonlyProof','Parent','readonlyBuffer s.proofAccount'),
 ('ReadonlyPublic','Parent','readonlyBuffer s.publicAccount'),
 ('Zero','CheckpointData','requireZero s.checkpointData')]:
 text='import NMT_R2_345Frames\n'+header+f'''
def step{name} (s : {frame}) (next : {frame} → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent ({expr})) (fun _ => next s)

theorem step{name}_valid (s : {frame}) (next : {frame} → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept ({expr})) suffix env (step{name} s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms step{name}_valid
end NMT_R2_345
'''
 (p/f'NMT_R2_345{name}.lean').write_text(text)
for name,frame,field,out,constructor,site in [
 ('CheckpointData','Parent','checkpointAccount','CheckpointData','⟨s,bytes⟩',1),
 ('PublicData','CheckpointData','publicAccount','PublicData','⟨s,bytes⟩',2)]:
 text='import NMT_R2_345Frames\n'+header+f'''
def step{name} (allocation : Allocation) (s : {frame}) (next : {out} → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (cloned (allocation {site}) s.{field}.bytes) (fun bytes => next {constructor})

theorem step{name}_valid (allocation : Allocation) (s : {frame})
 (next : {out} → Obs (Except ProgramError Bytes)) (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next {constructor})) :
 RS.bind (NMT_R2.data s.{field}) suffix env (step{name} allocation s next) := by
 exact try_valid _ _ _ _ env (cloned_valid _ _ env) later
#print axioms step{name}_valid
end NMT_R2_345
'''
 (p/f'NMT_R2_345{name}.lean').write_text(text)
