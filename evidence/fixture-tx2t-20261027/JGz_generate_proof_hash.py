"""Aggregate proof SHA using 15 opaque native chunks and 57 checked groups."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];name='JGz_ProofSHA'
out=[f'import JGz_SHAP{i:02}' for i in range(57)]+[f'import JGz_ProofNative{i:02}' for i in range(15)]+['import JGz_HashTools','set_option autoImplicit false',f'namespace AspisR1.{name}','open JFp_SHA256']
for i in range(14):
 out += [f'theorem regroup{i:02} : JGz_ProofNative{i:02}.chunks='+ ' ++ '.join(f'JGz_SHAP{4*i+j:02}.chunks' for j in range(4))+' := by rfl',f'#print axioms regroup{i:02}']
out += ['theorem lastGroup : JGz_ProofNative14.chunks ++ [JGz_SHAP56.B900.input]=JGz_SHAP56.chunks := by rfl','#print axioms lastGroup', 'def head : List (List Nat) := '+' ++ '.join(f'JGz_ProofNative{i:02}.chunks' for i in range(15)), 'def chunks : List (List Nat) := head ++ [JGz_SHAP56.B900.input]', 'def raw : List Nat := head.flatten ++ JGz_ProofNative14.tail', 'theorem headLength : head.length=900 := by', '  simp only [head,List.length_append]', '  change '+'+'.join(['64']*14+['4'])+'=900', '  rfl', '#print axioms headLength','theorem tailLength : JGz_ProofNative14.tail.length=7 := by rfl','#print axioms tailLength', 'theorem headLengths : ∀ b ∈ head,b.length=64 := by', '  intro b hb', '  simp only [head,List.mem_append] at hb', '  rcases hb with '+'|'.join(f'h{i}' for i in range(15))]
for i in range(14):
 out += [f'  · rw [regroup{i:02}] at h{i}',f'    simp only [List.mem_append] at h{i}',f'    rcases h{i} with h0|h1|h2|h3']
 for j in range(4):out += [f'    · exact JGz_SHAP{4*i+j:02}.lengths b h{j}']
out += ['  · simp only [JGz_ProofNative14.chunks,List.mem_cons,List.not_mem_nil,or_false] at h14', '    rcases h14 with h0|h1|h2|h3']+['    · subst b;rfl']*4
out += ['#print axioms headLengths','theorem rawLength : raw.length=57607 := by','  simp only [raw,List.length_append,JGz_HashTools.length_flatten head headLengths,headLength,tailLength]','#print axioms rawLength','theorem tailPad : JGz_ProofNative14.tail ++ [128] ++ List.replicate 48 0 ++ [0,0,0,0,0,7,8,56]=JGz_SHAP56.B900.input := by rfl','#print axioms tailPad','theorem padded : pad raw=chunks.flatten := by','  rw [pad,rawLength]', '  change (head.flatten ++ JGz_ProofNative14.tail) ++ [128] ++ List.replicate 48 0 ++ [0,0,0,0,0,7,8,56]=_', '  simp only [List.append_assoc]', '  rw [show JGz_ProofNative14.tail ++ ([128] ++ (List.replicate 48 0 ++ [0,0,0,0,0,7,8,56]))=JGz_SHAP56.B900.input from by simpa only [List.append_assoc] using tailPad]', '  simp only [chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]', '#print axioms padded', 'theorem lengths : ∀ b ∈ chunks,b.length=64 := by', '  intro b hb', '  simp only [chunks,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb', '  rcases hb with h|h', '  · exact headLengths b h', '  · subst b;rfl', '#print axioms lengths', 'attribute [local irreducible] '+' '.join(f'JGz_SHAP{i:02}.chunks' for i in range(57)), 'theorem checked : JFp_SHA256.hash raw=JGz_SHAP56.B900.result := by','  rw [JGz_HashTools.hash_chunks raw chunks padded lengths]','  unfold chunks head', '  rw ['+','.join(f'regroup{i:02}' for i in range(14))+']', '  simp only [List.append_assoc]', '  rw [lastGroup]', '  simp only [List.foldl_append]', '  rw [show initial=JGz_SHAP00.B000.start from rfl]']
for i in range(57):
 if i:out += [f'  rw [show JGz_SHAP{i-1:02}.B{16*i-1:03}.result=JGz_SHAP{i:02}.B{16*i:03}.start from rfl]']
 out += [f'  rw [JGz_SHAP{i:02}.folded]']
out += ['#print axioms checked',f'end AspisR1.{name}']
p=R/'lean'/(name+'.lean');s='\n'.join(out)+'\n'
if '--check' in sys.argv:assert p.read_text()==s,p
else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',name)
