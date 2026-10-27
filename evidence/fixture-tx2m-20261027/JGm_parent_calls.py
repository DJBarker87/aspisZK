from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]

def term(s):
 s=s.lstrip()
 if s[0]=='(':
  n=0
  for i,c in enumerate(s):
   n+=(c=='(')-(c==')')
   if n==0:return s[:i+1],s[i+1:]
 return s.split(' ',1)
for t,pre in [(0,'JGf'),(1,'JGh'),(2,'JGc')]:
 model=f'{pre}_TX2_M{t}Roots'
 text='\n'.join(p.read_text() for p in sorted((R/'lean').glob(f'{pre}_TX2_M{t}Level*.lean')))
 found=re.findall(r'theorem address(\d+) : BinMerkle32Path.nodeInput \(children (.*)\)=input\d+ := by rfl',text)
 ns=f'JGm_TX2_ParentCalls{t}'
 s=f'''import JGk_TX2_ParentWrite
import {pre}_TX2_M{t}Root
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open {model}
'''
 for n,args in found:
  l,r=term(args)
  r=r.strip()
  s+=f'''theorem source{n} {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (ni cursor : Usize) (index : U32) (w : Usize) (room : w.val<16) :
    reference.write_parent (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      s (encodeState {l}) (encodeState {r}) ni cursor index w=
      ok (.Next (JGk_TX2_ParentWrite.after s index w (encodeState value{n}) cursor)
        ni (JGk_TX2_ParentWrite.next w room)) :=
  JGk_TX2_ParentWrite.source D hash s {l} {r} value{n} ni cursor index w room
    ((congrArg JFp_SHADigest.digest address{n}).trans hash{n})
#print axioms source{n}
'''
 s+=f'end AspisR1.{ns}\nend\n'
 (R/f'lean/{ns}.lean').write_text(s)
 print(t,len(found))
