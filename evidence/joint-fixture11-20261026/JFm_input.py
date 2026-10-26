"""Symbolic compact-block expansion and bounded SHA input regrouping."""
from pathlib import Path
import re
P=Path(__file__).resolve().parent;R=P.parents[1]
ls=lambda xs:'['+','.join(map(str,xs))+']'
us=lambda xs:'['+','.join(str(x)+'#u8' for x in xs)+']'
def generate(i,prev,row):
 native=(R/f'lean/JFw_NativeRow{i:02}.lean').read_text();n,off=map(int,re.search(r'expandedPayload (\d+) (\d+)',native).groups())
 scan=re.search(r'(JFz_Scan\d+)\.canonical_selected',native)[1];text=(R/f'lean/{scan}.lean').read_text()
 payload=row['frame'][5:];parts=[payload[j:j+32] for j in range(0,len(payload),32)];assert len(parts)==n
 o=['namespace Input']
 for j,p in enumerate(parts):o += [f'def p{j:02} : List U8 := {us(p)}']
 nodes={};lemmas=[];at=0
 for m in re.finditer(r'def (b\d+) : List U8 := \[(.*?)\]',text):
  name=m[1];data=list(map(int,re.findall(r'(\d+)#u8',m[2])));k=len(data)//16;refs=[f'p{j:02}' for j in range(at,at+k)];nodes[name]=(k,refs);at+=k
  o += [f'theorem blocks_{name} : JFw_Blocks.blocks {k} {scan}.{name}=["PLACEHOLDER"] := by rfl'.replace('["PLACEHOLDER"]','['+','.join(refs)+']'),f'#print axioms blocks_{name}']
 for m in re.finditer(r'def (j\d+) : List U8 := (\w+) \+\+ (\w+)',text):
  name,left,right=m.groups();a,aa=nodes[left];b,bb=nodes[right];nodes[name]=(a+b,aa+bb)
  o += [f'theorem blocks_{name} : JFw_Blocks.blocks {a+b} {scan}.{name}=['+','.join(aa+bb)+'] := by',f'  rw [{scan}.{name},JFm_BlockSplit.append {a} {b} _ _ {scan}.{left}_length,blocks_{left},blocks_{right}]','  rfl',f'#print axioms blocks_{name}']
 root=re.search(r'def data : List U8 := (\w+)',text)[1];assert nodes[root][0]==n
 ps='['+','.join(f'p{j:02}' for j in range(n))+']'
 o += [f'def sourcePayload : List U8 := {ps}.flatten',f'theorem payloadBytes : JFw_NativeRow{i:02}.payload.val=sourcePayload := by',f'  change (JFw_Blocks.blocks {n} ((JFx_NativeBytes.proof.val.drop {off}).take {16*n})).flatten=_',f'  rw [{scan}.selected]',f'  unfold {scan}.data',f'  rw [blocks_{root}]','  rfl','#print axioms payloadBytes',f'theorem frameBytes : JFw_NativeRow{i:02}.record.val={us(row["frame"][:5])} ++ sourcePayload := by',f'  change _::_::_::_::_::JFw_NativeRow{i:02}.payload.val=_','  rw [payloadBytes]','  rfl','#print axioms frameBytes']
 segs=[row['before']+[0,160+i]+row['frame'][:5]]+parts
 for j,seg in enumerate(segs):
  o += [f'def n{j:02} : List Nat := {ls(seg)}']
  if j:o += [f'theorem cast{j:02} : (p{j-1:02}).map (fun x=>x.val)=n{j:02} := by rfl',f'#print axioms cast{j:02}']
 full=' ++ '.join(f'n{j:02}' for j in range(len(segs)));pay=' ++ '.join(f'n{j:02}' for j in range(1,len(segs)))
 o += ['def numeric : List Nat := '+full,'theorem payloadNat : sourcePayload.map (fun x=>x.val)='+pay+' := by','  simp only [sourcePayload,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc,'+','.join(f'cast{j:02}' for j in range(1,len(segs)))+']','#print axioms payloadNat',f'theorem prefixCast : ((encodeState {prev}).val.map (fun x=>x.val)) ++ [0,{160+i}] ++ {ls(row["frame"][:5])}=n00 := by rfl','#print axioms prefixCast']
 q=sum(map(len,segs))//64
 for block in range(q+1):
  offset=64*block;j=0
  while offset>=len(segs[j]):offset-=len(segs[j]);j+=1
  es=[f'(n{j:02}.drop {offset})' if offset else f'n{j:02}']+[f'n{k:02}' for k in range(j+1,len(segs))]
  o += [f'def rest{block:02} : List Nat := '+' ++ '.join(es)]
 for block in range(q):
  offset=64*block;j=0
  while offset>=len(segs[j]):offset-=len(segs[j]);j+=1
  consumed=[];todo=64
  while todo>0:
   consumed.append(f'n{j:02}');todo-=len(segs[j])-offset;j+=1;offset=0
  o += [f'theorem step{block:02} : rest{block:02}=JFm_Q{i:02}Absorb.B{block:02}.input ++ rest{block+1:02} := by','  simp only [rest'+f'{block:02},rest{block+1:02},'+','.join(consumed)+']','  rfl',f'#print axioms step{block:02}']
 o += [f'theorem last : rest{q:02}=JFm_Q{i:02}Absorb.tail := by','  simp only [rest'+f'{q:02},'+','.join(f'n{j:02}' for j in range(len(segs)-3,len(segs)))+']','  rfl','#print axioms last',f'theorem regroup : numeric=JFm_Q{i:02}Absorb.message := by',f'  change rest00=JFm_Q{i:02}Absorb.message','  rw ['+','.join(f'step{b:02}' for b in range(q))+',last]',f'  simp only [JFm_Q{i:02}Absorb.message,JFm_Q{i:02}Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]','#print axioms regroup',f'theorem native : (flatten (TranscriptStep.absorbParts (encodeState {prev}) {160+i}#u8 frame)).map Fin.val=numeric := by','  simp only [flatten,TranscriptStep.absorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,','    List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,frameBytes,payloadNat,List.map_cons,List.map_nil]',f'  change ((encodeState {prev}).val.map (fun x=>x.val)) ++ ([0,{160+i}] ++ ({ls(row["frame"][:5])} ++ ({pay})))=numeric',f'  have joined := congrArg (fun lead => lead ++ ({pay})) prefixCast','  simpa only [numeric,List.append_assoc] using joined','#print axioms native','end Input']
 return '\n'.join(o)+'\n'
