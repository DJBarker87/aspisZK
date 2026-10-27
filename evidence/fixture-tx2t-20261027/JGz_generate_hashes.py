"""SHA aggregation uses symbolic chunk lengths and named compression results."""
from pathlib import Path
import json,sys
R=Path(__file__).resolve().parents[2];files={};manifest=json.loads((Path(__file__).resolve().parent/'JGz_SHA_MANIFEST.json').read_text())
for kind,label,nfull,tailmod in [('P','Proof',900,'JGz_ProofNative14'),('U','Public',29,'JGz_PublicNative'),('C','Checksum',27,'JGz_ChecksumNative')]:
 if kind=='P':continue  # Proof uses the separately generated symbolic native-chunk join.
 modules=manifest[kind]['modules'];name=f'JGz_{label}SHA';length=manifest[kind]['bytes'];last=nfull;lastgroup=last//16
 out=[f'import {m}' for m in modules]+(['import JGz_SHAC0Fold'] if kind=='C' else [])+[f'import {tailmod}','import JGz_HashTools','set_option autoImplicit false',f'namespace AspisR1.{name}','open JFp_SHA256']
 headgroups=[f'{m}.chunks' for m in modules[:-1]]
 headtail='['+','.join(f'{modules[-1]}.B{i:03}.input' for i in range(lastgroup*16,nfull))+']'
 out += ['def head : List (List Nat) := '+' ++ '.join(headgroups+[headtail]),'def chunks : List (List Nat) := '+' ++ '.join(f'{m}.chunks' for m in modules), f'def raw : List Nat := head.flatten ++ {tailmod}.tail',f'theorem headLength : head.length={nfull} := by rfl','#print axioms headLength',f'theorem tailLength : {tailmod}.tail.length={length%64} := by rfl','#print axioms tailLength']
 out += ['theorem headLengths : ∀ b ∈ head,b.length=64 := by','  intro b hb','  simp only [head,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb','  rcases hb with '+'|'.join(f'h{i}' for i in range(len(headgroups)+nfull-lastgroup*16))]
 for i,m in enumerate(modules[:-1]):
  lengths='JGz_SHAC0Fold.lengths' if kind=='C' and i==0 else m+'.lengths'
  out += [f'  · exact {lengths} b h{i}']
 for i in range(nfull-lastgroup*16):out += ['  · subst b;rfl']
 out += ['#print axioms headLengths',f'theorem rawLength : raw.length={length} := by','  simp only [raw,List.length_append,JGz_HashTools.length_flatten head headLengths,headLength,tailLength]','#print axioms rawLength']
 bitbytes=list((8*length).to_bytes(8,'big'))
 out += [f'theorem tailPad : {tailmod}.tail ++ [128] ++ List.replicate {(55-length)%64} 0 ++ '+str(bitbytes).replace(' ','')+f'={modules[-1]}.B{last:03}.input := by rfl','#print axioms tailPad', 'theorem padded : pad raw=chunks.flatten := by','  rw [pad,rawLength]',f'  change (head.flatten ++ {tailmod}.tail) ++ [128] ++ List.replicate {(55-length)%64} 0 ++ '+str(bitbytes).replace(' ','')+'=_', '  simp only [List.append_assoc]', '  rw [show '+tailmod+'.tail ++ ([128] ++ (List.replicate '+str((55-length)%64)+' 0 ++ '+str(bitbytes).replace(' ','')+'))='+modules[-1]+f'.B{last:03}.input from by simpa only [List.append_assoc] using tailPad]', '  simp only [head,chunks,'+modules[-1]+'.chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]','#print axioms padded']
 out += ['theorem lengths : ∀ b ∈ chunks,b.length=64 := by','  intro b hb','  simp only [chunks,List.mem_append] at hb']
 if len(modules)>1:out+=['  rcases hb with '+'|'.join(f'h{i}' for i in range(len(modules)))]
 for i,m in enumerate(modules):
  lengths='JGz_SHAC0Fold.lengths' if kind=='C' and i==0 else m+'.lengths';out += [f'  · exact {lengths} b '+(f'h{i}' if len(modules)>1 else 'hb')]
 out += ['#print axioms lengths']
 if kind=='P':out += ['attribute [local irreducible] '+' '.join(m+'.chunks' for m in modules)]
 out += [f'theorem checked : JFp_SHA256.hash raw={modules[-1]}.B{last:03}.result := by','  rw [JGz_HashTools.hash_chunks raw chunks padded lengths]','  unfold chunks','  simp only [List.foldl_append]',f'  rw [show initial={modules[0]}.B000.start from rfl]']
 for i,m in enumerate(modules):
  if i:out += [f'  rw [show {modules[i-1]}.B{16*i-1:03}.result={m}.B{16*i:03}.start from rfl]']
  folded='JGz_SHAC0Fold.folded' if kind=='C' and i==0 else m+'.folded';out += ['  rw ['+folded+']']
 out += ['#print axioms checked',f'end AspisR1.{name}']
 files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n'
for p,s in files.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print(('checked' if '--check' in sys.argv else 'generated'),len(files),'hash-aggregation modules')
