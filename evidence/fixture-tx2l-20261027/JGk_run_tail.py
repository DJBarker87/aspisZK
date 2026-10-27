from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGk_TX2_Lookup15','JGk_TX2_Lookup16','JGk_TX2_Lookup17','JGk_TX2_SiblingLaws','JGk_TX2_LeafBinding','JGk_TX2_NativeRoots','JGk_TX2_ScratchIndices','JGk_TX2_CountSource','JGk_TX2_ZeroWindows','JGk_TX2_Padding0','JGk_TX2_Padding1','JGk_TX2_Padding2','JGk_TX2_AnyFalse','JGk_TX2_ParentWrite','JGk_TX2_ParentCalls0','JGk_TX2_ParentCalls1','JGk_TX2_ParentCalls2']
for n,mod in enumerate(mods,82):
 r=subprocess.run([sys.executable,str(P/'JGk_TX2_compile.py'),str(n),mod],stdout=(P/f'JGk_TX2_{n:03}-driver.log').open('w'),stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
