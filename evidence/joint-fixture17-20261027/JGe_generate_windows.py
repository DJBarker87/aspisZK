"""Bounded actual proof windows: max32 retained bytes per selection theorem."""
from pathlib import Path
import json,re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
def data(f):
 out=[]
 for l in f.read_text().splitlines():
  if l.startswith('def c'):
   if 'replicate' in l:
    n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',l).groups());out += [v]*n
   else:out+=list(map(int,re.findall(r'(\d+)#u8',l)))
 return out
raw=sum((data(R/f'lean/JFx_DataProof{i:02}.lean') for i in range(15)),[]);assert len(raw)==57607
base=['proofBytes','List.drop_append','List.take_append','List.length_append']+[f'JFx_DataProof{i:02}.length' for i in range(15)]+['Nat.reduceAdd','Nat.reduceSub','List.take_zero','List.append_nil','List.drop_zero','List.nil_append','List.drop_eq_nil_of_le','List.length_drop','Nat.reduceLeDiff','List.take_of_length_le']
files={};order=[];manifest=[]
for row,offset,n,width in [(27,7031,464,16),(29,7527,224,32),(30,7751,256,32),(31,8007,2048,32)]:
 cells=n//width
 for start in range(0,cells,8):
  mod=f'JGe_Window{row}_{start:02}';order.append(mod)
  out=['import JFw_Frames','set_option autoImplicit false',f'namespace AspisR1.JGe_Window{row}','open Aeneas Aeneas.Std Result JFx_NativeBytes','attribute [local irreducible] JFx_NativeBytes.proofBytes']
  for i in range(start,min(start+8,cells)):
   off=offset+width*i;chunk=raw[off:off+width]
   out += [f'def c{i:02} : List U8 := ['+','.join(f'{v}#u8' for v in chunk)+']',f'theorem selected{i:02} : (JFw_Frames.window {off} {width}).val=c{i:02} := by',f'  change (proofBytes.drop {off}).take {width}=c{i:02}','  simp only ['+','.join(base)+']']
   positions=[];acc=0
   for j in range(15):
    contents=data(R/f'lean/JFx_DataProof{j:02}.lean')
    if off<acc+len(contents) and acc<off+width:positions.append(j)
    acc+=len(contents)
   simp=[]
   for j in positions:
    src=(R/f'lean/JFx_DataProof{j:02}.lean').read_text()
    names=re.findall(r'^def (c\d+) :',src,re.M)
    simp += [f'JFx_DataProof{j:02}.bytes']+[f'JFx_DataProof{j:02}.{c}_length' for c in names]
   simp+=base[1:4]+base[-10:]
   out += ['  simp only ['+','.join(simp)+']','  rfl',f'#print axioms selected{i:02}']
   manifest.append({'row':row,'index':i,'offset':off,'width':width,'bytes':chunk})
  out += [f'end AspisR1.JGe_Window{row}'];files[R/'lean'/(mod+'.lean')]='\n'.join(out)+'\n'
files[P/'JGe_WINDOWS_MANIFEST.json']=json.dumps({'order':order,'cells':manifest},indent=2)+'\n'
for p,s in files.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(order),'modules;',len(manifest),'bounded source cells')
