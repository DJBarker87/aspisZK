"""Symbolic per-window native-byte glue; never normalise an entire buffer."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];files={}
for part in range(15):
 name=f'JGz_ProofNative{part:02}';data=f'JFx_DataProof{part:02}';first=64*part;count=64 if part<14 else 4
 groups=range(first//16,(first+count-1)//16+1)
 out=[f'import JGz_SHAP{g:02}' for g in groups]+[f'import {data}','set_option autoImplicit false',f'namespace AspisR1.{name}','open Aeneas Aeneas.Std']
 bs=[f'JGz_SHAP{b//16:02}.B{b:03}.input' for b in range(first,first+count)]
 out+=['def chunks : List (List Nat) := ['+','.join(bs)+']']
 if part==14:out+=['def tail : List Nat := '+str([int(x) for x in re.findall(r'(\d+)#u8',re.search(r'def c08.*?:=(.*)',(R/'lean'/f'{data}.lean').read_text())[1])]).replace(' ','')]
 for i,b in enumerate(bs):
  out += [f'theorem cell{i:02} : {b}=({data}.c{2*i:02} ++ {data}.c{2*i+1:02}).map (fun x=>x.val) := by rfl',f'#print axioms cell{i:02}']
 if part==14:out+=['theorem tail_native : '+data+'.c08.map (fun x=>x.val)=tail := by rfl','#print axioms tail_native']
 out += [f'theorem native : {data}.bytes.map (fun x=>x.val)=chunks.flatten'+(' ++ tail' if part==14 else '')+' := by','  unfold chunks','  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]','  rw ['+','.join(f'cell{i:02}' for i in range(count))+']']
 if part==14:out+=['  rw [←tail_native]']
 out += ['  simp only ['+data+'.bytes,List.map_append,List.append_assoc]','#print axioms native',f'end AspisR1.{name}']
 files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n'
name='JGz_PublicNative';data='JFx_DataPublic00';count=29
out=['import JGz_SHAU00','import JGz_SHAU01',f'import {data}','set_option autoImplicit false',f'namespace AspisR1.{name}','open Aeneas Aeneas.Std']
bs=[f'JGz_SHAU{b//16:02}.B{b:03}.input' for b in range(count)]
out+=['def chunks : List (List Nat) := ['+','.join(bs)+']','def tail : List Nat := '+str([int(x) for x in re.findall(r'(\d+)#u8',re.search(r'def c58.*?:=(.*)',(R/'lean'/f'{data}.lean').read_text())[1])]).replace(' ','')]
for i,b in enumerate(bs):out += [f'theorem cell{i:02} : {b}=({data}.c{2*i:02} ++ {data}.c{2*i+1:02}).map (fun x=>x.val) := by rfl',f'#print axioms cell{i:02}']
out += [f'theorem tail_native : {data}.c58.map (fun x=>x.val)=tail := by rfl','#print axioms tail_native',f'theorem native : {data}.bytes.map (fun x=>x.val)=chunks.flatten ++ tail := by','  unfold chunks','  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]','  rw ['+','.join(f'cell{i:02}' for i in range(count))+']','  rw [←tail_native]',f'  simp only [{data}.bytes,List.map_append,List.append_assoc]','#print axioms native',f'end AspisR1.{name}']
files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n'
for p,s in files.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print(('checked' if '--check' in sys.argv else 'generated'),len(files),'native glue modules')
