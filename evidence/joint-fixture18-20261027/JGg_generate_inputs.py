"""Match source payload chunks to certified SHA messages with opaque tails."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
diag=json.loads((P.parent/'joint-fixture17-20261027/JGe_OPENING_DIAGNOSTIC.json').read_text());files={};ls=lambda x:'['+','.join(map(str,x))+']'
for row in [27,29,30,31]:
 msg=diag['messages'][f'Q{row}Absorb'];segs=[msg[:38]]+[msg[i:i+32] for i in range(38,len(msg),32)];n=len(segs);nf=len(msg)//64
 mod=f'JGg_Input{row}';ns='AspisR1.'+mod
 before='JGe_OpeningInit.state' if row==27 else f'JFp_SHADigest.output JGe_Q{row-1}Ratchet0.result'
 out=[f'import JGe_Payload{row}',f'import JGe_Q{row}Absorb','import JGe_OpeningInit']
 if row!=27:out += [f'import JGe_Q{row-1}Ratchet0']
 out += ['set_option autoImplicit false',f'namespace {ns}','open Aeneas Aeneas.Std Result AspisR1PublicPreparation','open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge',f'open JGe_Window{row}',f'def before : State := {before}',f'def payload : Slice U8 := JGe_Payload{row}.value']
 for i,seg in enumerate(segs):out += [f'def n{i:02} : List Nat := {ls(seg)}']
 for i in range(n-1):
  expr=f'(c{i:02} ++ List.replicate 16 0#u8)' if row==27 else f'c{i:02}'
  out += [(f'theorem cast{i:02} : c{i:02}.map (fun x=>x.val) ++ (List.replicate 16 0#u8).map (fun x=>x.val)=n{i+1:02} := by rfl' if row==27 else f'theorem cast{i:02} : {expr}.map (fun x=>x.val)=n{i+1:02} := by rfl'),f'#print axioms cast{i:02}']
 expr=' ++ '.join(f'n{i:02}' for i in range(1,n))
 out += [f'theorem payloadNat : payload.val.map (fun x=>x.val)={expr} := by']
 if row==27:
  out += ['  rw [show payload.val=JGe_Payload27.sourceChunks.flatten from JGe_Payload27.bytes]','  simp only [JGe_Payload27.sourceChunks,JGe_Payload27.rawChunks,List.map_cons,List.map_nil]']
 else:out += [f'  rw [show payload.val=JGe_Payload{row}.rawChunks.flatten from JGe_Payload{row}.retained]','  simp only [JGe_Payload'+str(row)+'.rawChunks]']
 out += ['  simp only [List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,'+','.join(f'cast{i:02}' for i in range(n-1))+']','  <;> simp only [List.append_assoc]','#print axioms payloadNat',f'theorem prefixCast : (encodeState before).val.map (fun x=>x.val) ++ [0,{160+row}] ++ ['+','.join(map(str,list((len(msg)-38).to_bytes(4,'little'))))+']=n00 := by rfl','#print axioms prefixCast','def numeric : List Nat := '+' ++ '.join(f'n{i:02}' for i in range(n))]
 out += [f'def suffix{n:03} : List Nat := []']
 for i in reversed(range(n)):out += [f'def suffix{i:03} : List Nat := n{i:02} ++ suffix{i+1:03}']
 attrs='attribute [local irreducible] '+' '.join(f'suffix{i:03}' for i in range(n+1));out += [attrs]
 positions=[]
 for b in range(nf+1):
  off=64*b;j=0
  while off>=len(segs[j]):off-=len(segs[j]);j+=1
  positions.append((j,off))
  out += [f'def rest{b:02} : List Nat := '+(f'n{j:02}.drop {off}' if off else f'n{j:02}')+f' ++ suffix{j+1:03}']
 out += ['theorem numeric_eq : numeric=rest00 := by','  simp only [numeric,rest00,List.append_assoc,List.append_nil,'+','.join(f'suffix{i:03}' for i in range(1,n+1))+']','#print axioms numeric_eq']
 for b in range(nf):
  j,off=positions[b];first=j;todo=64;terms=[]
  while todo>0:
   terms.append(f'(n{j:02}.drop {off})' if off else f'n{j:02}');todo-=len(segs[j])-off;j+=1;off=0
  drop=len(segs[j-1])+todo;unfold=','.join(f'suffix{k:03}' for k in range(first+1,j))
  out += [f'theorem step{b:02} : rest{b:02}=JGe_Q{row}Absorb.B{b:02}.input ++ rest{b+1:02} := by','  have cell : '+' ++ '.join(terms)+f'=JGe_Q{row}Absorb.B{b:02}.input ++ (n{j-1:02}.drop {drop}) := by rfl',f'  simpa only [rest{b:02},rest{b+1:02},{unfold},List.append_assoc] using',f'    congrArg (fun t : List Nat => t ++ suffix{j:03}) cell',f'#print axioms step{b:02}']
 j,off=positions[-1];out += [f'theorem last : rest{nf:02}=JGe_Q{row}Absorb.tail := by',f'  simp only [rest{nf:02},'+','.join(f'suffix{k:03}' for k in range(j+1,n+1))+f',n{j:02}]','  rfl','#print axioms last','theorem regroup : numeric=JGe_Q'+str(row)+'Absorb.message := by','  rw [numeric_eq]','  rw ['+','.join(f'step{b:02}' for b in range(nf))+',last]','  simp only [JGe_Q'+str(row)+'Absorb.message,JGe_Q'+str(row)+'Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]','#print axioms regroup']
 out += [f'theorem lengthCast : (core.num.U32.to_le_bytes {len(msg)-38}#u32).val.map (fun x=>x.val)={ls(list((len(msg)-38).to_bytes(4,"little")))} := by', "  simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac", '#print axioms lengthCast']
 out += [f'theorem native : (flatten (CallerStep.openingAbsorbParts (encodeState before) {160+row}#u8 {len(msg)-38}#u32 payload)).map Fin.val=JGe_Q{row}Absorb.message := by','  rw [←regroup]','  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,payloadNat,lengthCast,List.map_cons,List.map_nil]','  change (encodeState before).val.map (fun x=>x.val) ++ ([0,'+str(160+row)+'] ++ ('+ls(list((len(msg)-38).to_bytes(4,'little')))+' ++ ('+expr+')))=numeric','  have h := congrArg (fun lead => lead ++ ('+expr+')) prefixCast','  simpa only [numeric,List.append_assoc] using h','#print axioms native',f'end {ns}']
 files[R/'lean'/(mod+'.lean')]='\n'.join(out)+'\n'
for p,s in files.items():
 if '--check' in sys.argv:
  checked_path=p if p.exists() else p
  assert checked_path.read_text()==s,checked_path
 else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(files),'source input modules')
