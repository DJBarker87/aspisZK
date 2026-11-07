from pathlib import Path
p=Path('evidence/phys-adapter-20261111/NNE_AcceptedCuts.lean').read_text().replace('namespace NNE_AcceptedCuts','namespace NNE_RslOk').replace('end NNE_AcceptedCuts','end NNE_RslOk')
p=p.replace(' (stage : TX1_344.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState))\n (packet : TX1_344.RowSpec_344 V P C stage)\n','').replace(' (stage : TX2_240.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState))\n (packet : TX2_240.RowSpec_240 L D V stage)\n','')
p=p.replace(' (accepted : stage a s env = ⟨.ret (.ok (),post),es⟩)', ' (h : TX1_344.Ref V P C a s env ⟨.ret (.ok (),post),es⟩)',1)
p=p.replace(' have h := packet a s env trivial\n rw [accepted] at h\n','',1)
p=p.replace(' (domain : TX2_240.Domain V a s)\n (accepted : stage a s env = ⟨.ret (.ok (),post),es⟩)', ' (h : TX2_240.Ref L D V a s env ⟨.ret (.ok (),post),es⟩)',1)
p=p.replace(' have h := packet a s env domain\n rw [accepted] at h\n','',1)
Path('evidence/phys-adapter-20261111/NNE_RslOk.lean').write_text(p)
