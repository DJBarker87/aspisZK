from pathlib import Path
import re,json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
source=(R/'lean/JFs_SerializedBytes.lean').read_text().split('def chunks : List (List U8) := [',1)[1].split(']\ndef bytes',1)[0]
items=[x.strip().removesuffix(',') for x in source.splitlines() if x.strip()]
msg=json.loads((P/'JFp_SHA_INPUT.json').read_text())['message'];ls=lambda xs:'['+','.join(map(str,xs))+']'
expr=['AspisR1PublicPreparation.r1_wire.DOMAIN.val','[0#u8]','(core.num.U32.to_le_bytes 1455#u32).val']+items+['root.val']
lengths=[38,1,4]+[32 if 'Digest' in x else len(re.findall(r'\d+#u8',x)) for x in items]+[32]
assert sum(lengths)==1530
out=['import JFs_ExactInitialization','import JFp_SeedHash','set_option autoImplicit false','namespace AspisR1.JFp_InitBytes','open Aeneas Aeneas.Std Result','open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge','open AspisR1PublicPreparation', 'def root : Array U8 32#usize := ⟨['+','.join(f'{x}#u8' for x in msg[-32:])+'],by rfl⟩']
at=0;segs=[]
for i,(ex,n) in enumerate(zip(expr,lengths)):
 d=msg[at:at+n];at+=n;segs.append(d)
 out += [f'def n{i:02} : List Nat := {ls(d)}',f'theorem cast{i:02} : ({ex}).map (fun x => x.val)=n{i:02} := by rfl',f'#print axioms cast{i:02}']
out += ['def numeric : List Nat := '+ ' ++ '.join(f'n{i:02}' for i in range(len(segs)))]
# Named source suffixes, always retaining unconsumed chunks symbolically.
for block in range(24):
 start=64*block;off=start;j=0
 while off>=len(segs[j]):off-=len(segs[j]);j+=1
 es=[f'(n{j:02}.drop {off})' if off else f'n{j:02}']+[f'n{k:02}' for k in range(j+1,len(segs))]
 out += [f'def rest{block:02} : List Nat := '+' ++ '.join(es)]
 if block<23:
  consumed=[];a=64;ii=j;oo=off
  while a>0:
   consumed.append(f'n{ii:02}');a-=len(segs[ii])-oo;ii+=1;oo=0
  out += [f'theorem step{block:02} : rest{block:02}=JFp_SHABlock{block:02}.input ++ rest{block+1:02} := by',f'  simp only [rest{block:02},rest{block+1:02},'+','.join(consumed)+']','  rfl',f'#print axioms step{block:02}']
# definitions of next suffix must precede theorem; reorder later
text='\n'.join(out)+'\n'
# Move every step theorem behind all rest definitions.
steps=re.findall(r'theorem step.*?#print axioms step\d+\n',text,re.S)
# non-greedy first match starts exact theorem
for st in steps:text=text.replace(st,'')
text+=''.join(steps)
text+='theorem last : rest23=JFp_SeedHash.tail := by\n  simp only [rest23,'+','.join(f'n{i:02}' for i in range(len(segs)-3,len(segs)))+']\n  rfl\n#print axioms last\n'
text+='theorem regroup : numeric=JFp_SeedHash.raw := by\n  change rest00=JFp_SeedHash.raw\n  rw ['+','.join(f'step{i:02}' for i in range(23))+',last]\n  simp only [JFp_SeedHash.raw,JFp_SeedHash.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]\n#print axioms regroup\n'
text+='''theorem native :
    (flatten (TranscriptStep.initParts (alloc.vec.Vec.deref JFs_ExactSerialization.encoded) root 1455#u32)).map Fin.val = numeric := by
  simp only [flatten,TranscriptStep.initParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,alloc.vec.Vec.deref,JFs_ExactSerialization.encoded,
    JFs_SerializedBytes.bytes,JFs_SerializedBytes.chunks,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,decodeByte,
'''+','.join(f'    cast{i:02}' for i in range(len(segs)))+''',numeric]
#print axioms native
end AspisR1.JFp_InitBytes
'''
f=R/'lean/JFp_InitBytes.lean'
if '--check' in sys.argv:assert f.read_text()==text
else:f.write_text(text)
print('input chunks',len(segs))
