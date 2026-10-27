"""Native real-byte leaves via bounded 32-byte selections and symbolic 64-byte regrouping."""
from pathlib import Path
import re,json,sys
P=Path(__file__).resolve().parent; R=P.parents[1]
data=json.loads((R/'evidence/joint-fixture24-20261027/JGr_MERKLE_PREFLIGHT.json').read_text())
ls=lambda xs:'['+','.join(map(str,xs))+']'
u8=lambda xs:'['+','.join(f'{x}#u8' for x in xs)+']'
prune=['JFx_NativeBytes.proof','JFx_NativeBytes.proofBytes']+[f'JFx_DataProof{i:02}.length' for i in range(15)]
cleanup=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceMul','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
files={}
for kind in range(3):
 for i,row in enumerate(data['trees'][kind]['hashes'][:10]):
  pos=i; name=f'JGu_M{kind}Leaf{pos:02}'; hn=f'JGr_M{kind}.Hash{i:03}'; ro=f'JGr_M{kind}Roots'
  nc=16 if kind==0 else 5; nv=nc-1; vs=[0,480,672][kind]; ss=[608,640,800][kind]; tag=[113,241,114][kind]
  s=f'import {f"JGr_M{kind}Leaves"}\nimport JGc_TX2_LeafHelpers\nimport JGp_Opening{pos}\nset_option autoImplicit false\nset_option linter.unusedSimpArgs false\nnoncomputable section\nnamespace AspisR1.{name}\nopen Aeneas Aeneas.Std Result\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge\n'
  for j in range(nc):
   bs=row['message'][2+32*j:2+32*(j+1)]; start=vs+32*j if j<nv else ss; off=10055+832*pos+start
   s+=f'def c{j} : List U8 := {u8(bs)}\ndef n{j} : List Nat := {ls(bs)}\ntheorem cast{j} : (c{j}.map decodeByte).map Fin.val=n{j} := by rfl\n#print axioms cast{j}\n'
   s+=f'theorem select{j} : ((JFo_Opening.value ⟨{pos},by decide⟩).val.drop {start}).take 32=c{j} := by\n  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 {start} 32 (by decide)]\n'
   s+='  simp only ['+','.join(prune+cleanup)+']\n';more=[]
   for k in range(off//4096,(off+31)//4096+1):
    mod=f'JFx_DataProof{k:02}';text=(R/'lean'/(mod+'.lean')).read_text();more += [mod+'.bytes']+[mod+'.'+x for x in re.findall(r'theorem (c\d+_length)',text)]
   s+='  simp only ['+','.join(more+cleanup)+f']\n  rfl\n#print axioms select{j}\n'
  cs='++'.join(f'c{j}' for j in range(nv))
  s+=f'theorem values : ((JFo_Opening.value ⟨{pos},by decide⟩).val.drop {vs}).take {32*nv}={cs} := by\n'
  s+=f'  have split : ((JFo_Opening.value ⟨{pos},by decide⟩).val.drop {vs}).take {32*nv}='+ '++'.join(f'(((JFo_Opening.value ⟨{pos},by decide⟩).val.drop {vs}).drop {32*j}).take 32' for j in range(nv))+' := by\n'
  s+='    rw ['+','.join(f'List.take_add (i:=32) (j:={32*j})' for j in range(nv-1,0,-1))+']\n    simp only [List.drop_drop,Nat.reduceAdd,List.append_assoc,List.drop_zero]\n'
  s+='  simpa only [List.drop_drop,Nat.reduceAdd,'+','.join(f'select{j}' for j in range(nv))+'] using split\n#print axioms values\n'
  s+=f'def numeric : List Nat := [16,{tag}]++'+ '++'.join(f'n{j}' for j in range(nc))+'\n'
  nb=(len(row['message'])//64)
  for b in range(nb):
   rest='++'.join([f'n{2*b+1}.drop 30']+[f'n{j}' for j in range(2*b+2,nc)])
   s+=f'def rest{b+1} : List Nat := {rest}\n'
  s+=f'theorem regroup : numeric={hn}.message := by\n'
  for b in range(nb):
   start=f'[16,{tag}]++n0++n1' if b==0 else f'n{2*b-1}.drop 30++n{2*b}++n{2*b+1}'
   s+=f'  have step{b} : {start}={hn}.B{b:02}.input++n{2*b+1}.drop 30 := by rfl\n'
   fr='numeric' if b==0 else f'rest{b}'
   after='++'.join(f'n{j}' for j in range(2*b+2,nc))
   s+=f'  have h{b} : {fr}={hn}.B{b:02}.input++rest{b+1} := by\n'
   if after:s+=f'    simpa only [{fr},rest{b+1},List.append_assoc] using congrArg (fun xs : List Nat => xs++{after}) step{b}\n'
   else:s+=f'    exact step{b}\n'
  s+=f'  have tail : rest{nb}={hn}.tail := by rfl\n  rw ['+','.join(f'h{b}' for b in range(nb))+',tail]\n'
  s+=f'  simp only [{hn}.message,{hn}.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]\n#print axioms regroup\n'
  s+=f'theorem address : (flatten (Port4B_LeafCode.input {kind}#usize (JFo_Opening.value ⟨{pos},by decide⟩))).map Fin.val={hn}.message := by\n  rw [Port4B_LeafCode.input,'+('if_pos (by rfl : 0#usize=0#usize)' if kind==0 else ('if_neg (by decide : ¬1#usize=0#usize),if_pos (by rfl : 1#usize=1#usize)' if kind==1 else 'if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)'))+']\n'
  s+='  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]\n'
  s+=f'  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨{pos},by decide⟩) {vs}#usize {vs+32*nv}#usize).val={cs} := values\n'
  s+=f'  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨{pos},by decide⟩) {ss}#usize {ss+32}#usize).val=c{nc-1} := select{nc-1}\n  rw [hv,hs]\n'
  s+='  simp only [List.map_append,List.map_cons,List.map_nil,'+','.join(f'cast{j}' for j in range(nc))+']\n'
  s+=f'  have h16 : (16#u8).val=16 := by scalar_tac\n  have htag : ({tag}#u8).val={tag} := by scalar_tac\n  simpa only [numeric,List.append_assoc,decodeByte,h16,htag] using regroup\n#print axioms address\n'
  s+=f'''theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {{D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}}
      hash {kind}#usize (JFo_Opening.value ⟨{pos},by decide⟩)=ok (encodeState {ro}.value{i:03}) := by
  rw [show Port4B_LeafCode.native _ hash {kind}#usize (JFo_Opening.value ⟨{pos},by decide⟩)=
    ({{D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input {kind}#usize (JFo_Opening.value ⟨{pos},by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input {kind}#usize (JFo_Opening.value ⟨{pos},by decide⟩)))))=_
  have same : flatten (Port4B_LeafCode.input {kind}#usize (JFo_Opening.value ⟨{pos},by decide⟩))={ro}.input{i:03} :=
    (List.map_inj_right (fun _ _ h => Fin.val_injective h)).mp (address.trans {ro}.numeric{i:03}.symm)
  rw [same,{ro}.hash{i:03}]
#print axioms source
end AspisR1.{name}
end
'''
  files[R/'lean'/(name+'.lean')]=s
paired={}
for kind in range(3):
 for pos in range(0,10,2):
  texts=[files[R/'lean'/f'JGu_M{kind}Leaf{k:02}.lean'] for k in range(pos,pos+2)]
  imports=sorted({line for text in texts for line in text.splitlines() if line.startswith('import ')})
  paired[R/'lean'/f'JGu_M{kind}LeafSources{pos:02}.lean']='\n'.join(imports)+'\n'+''.join(text[text.index('set_option'):] for text in texts)
files=paired
for f,s in files.items():
 if '--check' in sys.argv: assert f.read_text()==s,f
 else:f.write_text(s)
print('leaf generator:',len(files),'modules, each native address uses bounded32-byte selections')
