"""Nine bounded zero windows per real native padding slice, then symbolic assembly."""
from pathlib import Path
import re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
prune=['JFx_NativeBytes.proof','JFx_NativeBytes.proofBytes']+[f'JFx_DataProof{i:02}.length' for i in range(15)]
cleanup=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceMul','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
files={}
for kind,start,count,cap in [(0,41799,163,172),(1,47303,163,172),(2,52807,141,150)]:
 name=f'JGh_TX2_Padding{kind}'
 s='import JGh_TX2_ZeroWindows\nset_option autoImplicit false\nnamespace AspisR1.'+name+'\nopen Aeneas Aeneas.Std Result\n'
 s+=f'def padding : List U8 := JGh_TX2_NodeViews.nodes{kind}.val.drop {32*count}\n'
 for j in range(9):
  off=start+32*(count+j)
  s+=f'theorem window{j} : (padding.drop {32*j}).take 32=List.replicate 32 0#u8 := by\n  rw [padding,List.drop_drop,JGh_TX2_NodeViews.values{kind},JFq_Range.nested _ _ {32*cap} {32*count}+{32*j} 32 (by decide)]\n'
  # Parenthesize the summed argument to nested, keeping the source expression shape.
  s=s.replace(f'{32*cap} {32*count}+{32*j} 32',f'{32*cap} ({32*count}+{32*j}) 32')
  s+='  simp only ['+','.join(prune+cleanup)+']\n';more=[]
  for k in range(off//4096,(off+31)//4096+1):
   mod=f'JFx_DataProof{k:02}';text=(R/'lean'/(mod+'.lean')).read_text();more += [mod+'.bytes']+[mod+'.'+x for x in re.findall(r'theorem (c\d+_length)',text)]
  s+='  simp only ['+','.join(more+cleanup)+f']\n  rfl\n#print axioms window{j}\n'
 s+=f'theorem size : padding.length=288 := by\n  rw [padding,List.length_drop,JGh_TX2_NodeViews.length{kind}]\n  rfl\n#print axioms size\n'
 s+='theorem source : padding=List.replicate 288 0#u8 := by\n  apply JGh_TX2_ZeroWindows.source 9 padding size\n  intro i hi\n  interval_cases i\n'
 for j in range(9):s+=f'  · exact window{j}\n'
 s+=f'#print axioms source\nend AspisR1.{name}\n'
 files[R/'lean'/(name+'.lean')]=s
for f,s in files.items():
 if '--check' in sys.argv:assert (f if f.exists() else P/'JGh_UNCHECKED'/(f.name+'.txt')).read_text()==s,f
 else:f.write_text(s)
print('padding generator: three modules, nine32-byte windows each')
