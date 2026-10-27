"""Connect named SHA certificates to the SAME JFp_SHADigest oracle world."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];files={}
for label,kind,count,hashname in [('Proof','P',57,'proofHash'),('Public','U',2,'publicHash'),('Checksum','C',2,'checksum')]:
 name=f'JGz_{label}Digest';sha=f'JGz_{label}SHA';last={'P':900,'U':29,'C':27}[kind]
 imports=[sha,'JFn_HashBoundary','JFp_SHADigest']+([f'JGz_ProofNative{i:02}' for i in range(14)] if kind=='P' else [])
 out=[f'import {x}' for x in imports]+['set_option autoImplicit false',f'namespace AspisR1.{name}','open Aeneas Aeneas.Std Result','open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge']
 parts={'P':'proofParts','U':'publicParts','C':'checksumParts'}[kind]
 out += [f'theorem native : (flatten JFn_HashBoundary.{parts}).map Fin.val={sha}.raw := by']
 basic=['flatten',f'JFn_HashBoundary.{parts}','Array.to_slice','Array.make','List.flatMap_cons','List.flatMap_nil','List.append_nil','List.map_append','List.map_map','Function.comp_def','decodeByte','id_eq']
 if kind=='P':
  basic +=['JFx_NativeBytes.proof','JFx_NativeBytes.proofBytes']
  out += ['  simp only ['+','.join(basic)+']','  rw ['+','.join(f'JGz_ProofNative{i:02}.native' for i in range(15))+']']
  unfold=[f'{sha}.raw',f'{sha}.head']+[f'JGz_ProofNative{i:02}.chunks' for i in range(15)]+[f'JGz_SHAP{i:02}.chunks' for i in range(56)]
 elif kind=='U':
  basic +=['JFx_NativeBytes.publicInput','JFx_NativeBytes.publicBytes']
  out += ['  simp only ['+','.join(basic)+']','  rw [JGz_PublicNative.native]']
  unfold=[f'{sha}.raw',f'{sha}.head','JGz_PublicNative.chunks','JGz_SHAU00.chunks']
 else:
  basic +=['JFq_Range.segment','JFx_NativeBytes.checkpoint','JFx_NativeBytes.checkpointBytes','List.drop_zero']
  out += ['  simp only ['+','.join(basic)+']','  change (JGz_ChecksumNative.domain ++ JFx_DataCheckpoint00.bytes.take 1736).map (fun x=>x.val)=_', '  rw [JGz_ChecksumNative.native]']
  unfold=[f'{sha}.raw',f'{sha}.head','JGz_ChecksumNative.raw','JGz_ChecksumNative.chunks','JGz_SHAC00.chunks']
 out += ['  simp only ['+','.join(unfold+['List.flatten_append','List.flatten_cons','List.flatten_nil','List.append_nil','List.append_assoc'])+']','#print axioms native']
 out += [f'theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.{parts})=decodeState JFo_AuthBytes.{hashname} := by','  unfold JFp_SHADigest.digest',f'  rw [native,{sha}.checked]','  funext i','  fin_cases i <;> rfl','#print axioms source',f'end AspisR1.{name}']
 files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n'
p=R/'lean/JGz_Realizes.lean';files[p]='''import JGz_ProofDigest
import JGz_PublicDigest
import JGz_ChecksumDigest
set_option autoImplicit false
namespace AspisR1.JGz_Realizes
/-- Mathematical SHA256 on the exact same three native requests used by the
retained TX2 reader. This is not a syscall or source-to-ELF refinement. -/
theorem source : JFn_HashBoundary.Realizes JFp_SHADigest.digest :=
  ⟨JGz_ProofDigest.source,JGz_PublicDigest.source,JGz_ChecksumDigest.source⟩
#print axioms source
end AspisR1.JGz_Realizes
'''
for p,s in files.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print(('checked' if '--check' in sys.argv else 'generated'),len(files),'exact-oracle modules')
