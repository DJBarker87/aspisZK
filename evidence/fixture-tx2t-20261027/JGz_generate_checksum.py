"""Checksum glue at the 22-byte domain offset, with symbolic split joins."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];data='JFx_DataCheckpoint00';name='JGz_ChecksumNative'
source=(R/'lean'/f'{data}.lean').read_text();cp=[]
for line in source.splitlines():
 if re.match(r'def c\d+ :',line):
  t=line.split(':=',1)[1]
  if 'List.replicate' in t:
   n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',t).groups());cp += [v]*n
  else:cp +=list(map(int,re.findall(r'(\d+)#u8',t)))
domain=[85,78,80,82,79,86,69,68,58,82,49,58,99,104,101,99,107,112,111,105,110,116];raw=domain+cp[:1736]
ls=lambda xs:'['+','.join(map(str,xs))+']'
out=['import JGz_SHAC00','import JGz_SHAC01',f'import {data}','set_option autoImplicit false',f'namespace AspisR1.{name}','open Aeneas Aeneas.Std', 'def domain : List U8 := ['+','.join(f'{v}#u8' for v in domain)+']', 'def chunks : List (List Nat) := ['+','.join(f'JGz_SHAC{b//16:02}.B{b:03}.input' for b in range(27))+']', 'def tail : List Nat := '+ls(raw[1728:]),'def raw : List Nat := chunks.flatten ++ tail']
for i in range(27):
 pieces=['domain',data+'.c00',data+'.c01.take 10'] if i==0 else [f'{data}.c{2*i-1:02}.drop 10',f'{data}.c{2*i:02}',f'{data}.c{2*i+1:02}.take 10']
 out += [f'theorem cell{i:02} : JGz_SHAC{i//16:02}.B{i:03}.input=('+ ' ++ '.join(pieces)+').map (fun x=>x.val) := by rfl',f'#print axioms cell{i:02}']
out += [f'theorem tail_native : tail=({data}.c53.drop 10 ++ {data}.c54.take 8).map (fun x=>x.val) := by rfl','#print axioms tail_native',f'def prefix : List U8 := '+ ' ++ '.join(f'{data}.c{i:02}' for i in range(54))+f' ++ {data}.c54.take 8',f'theorem cut : {data}.bytes.take 1736=prefix := by','  simp only ['+data+'.bytes,prefix,List.take_append,List.length_append,'+','.join(f'{data}.c{i:02}_length' for i in range(56))+',Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.take_of_length_le,List.take_zero,List.append_nil]','  rfl','#print axioms cut', 'theorem split_join {A : Type} (xs rest : List A) (n : Nat) : xs.take n ++ (xs.drop n ++ rest)=xs ++ rest := by','  rw [←List.append_assoc,List.take_append_drop]','#print axioms split_join',f'theorem native : (domain ++ {data}.bytes.take 1736).map (fun x=>x.val)=raw := by','  rw [cut]','  unfold raw chunks','  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]','  rw ['+','.join(f'cell{i:02}' for i in range(27))+',tail_native]','  simp only [prefix,List.map_append,List.map_take,List.map_drop,List.append_assoc,split_join]','#print axioms native',f'end AspisR1.{name}']
p=R/'lean'/(name+'.lean');s='\n'.join(out)+'\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',name)
