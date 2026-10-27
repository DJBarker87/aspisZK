"""Bind each folded leaf hash to five real32-byte windows; no whole opening reduction."""
from pathlib import Path
import re,json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
tree=json.loads((P/'JGc_MERKLE_PREFLIGHT.json').read_text())['trees'][2]
files={};ls=lambda xs:'['+','.join(map(str,xs))+']';u8=lambda xs:'['+','.join(f'{x}#u8' for x in xs)+']'
prune=['JFx_NativeBytes.proof','JFx_NativeBytes.proofBytes']+[f'JFx_DataProof{i:02}.length' for i in range(15)]
cleanup=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceMul','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
for i,row in enumerate(tree['hashes'][:12]):
 pos=10+i;name=f'JGc_TX2_M2Leaf{pos:02}';hashn=f'JGc_TX2_M2.Hash{i:03}';ro='JGc_TX2_M2Roots'
 s=f'import JGc_TX2_M2Leaves\nimport JGc_TX2_LeafHelpers\n'+''.join(f'import JFn_Value{pos}_{j}\n' for j in range(4))
 s+='set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+name+'\nopen Aeneas Aeneas.Std Result\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge\n'
 chunks=[row['message'][2+32*j:2+32*(j+1)] for j in range(5)]
 for j,bs in enumerate(chunks):
  if j<4:s+=f'def c{j} : List U8 := JFn_Value{pos}_{j}.bytes\n'
  else:s+=f'def c{j} : List U8 := {u8(bs)}\n'
  s+=f'def n{j} : List Nat := {ls(bs)}\ntheorem cast{j} : (c{j}.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n{j} := by rfl\n#print axioms cast{j}\n'
 off=10055+832*pos+800
 s+=f'theorem salt : ((JFo_Opening.value ⟨{pos},by decide⟩).val.drop 800).take 32=c4 := by\n'
 s+=f'  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]\n'
 s+='  simp only ['+','.join(prune+cleanup)+']\n'
 # only the source chunks that intersect this32-byte interval are expanded
 lo,hi=off//4096,(off+31)//4096
 more=[]
 for k in range(lo,hi+1):
  mod=f'JFx_DataProof{k:02}';text=(R/'lean'/(mod+'.lean')).read_text();more+=[mod+'.bytes']+re.findall(r'theorem (c\d+_length)',text)
  more=[(mod+'.'+x if x.startswith('c') else x) for x in more]
 s+='  simp only ['+','.join(more+cleanup)+']\n  rfl\n#print axioms salt\n'
 s+=f'''theorem values : ((JFo_Opening.value ⟨{pos},by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨{pos},by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value{pos}_0.selected JFn_Value{pos}_1.selected JFn_Value{pos}_2.selected JFn_Value{pos}_3.selected
#print axioms values
'''
 s+='def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4\n'
 s+='def rest1 : List Nat := n1.drop 30++n2++n3++n4\ndef rest2 : List Nat := n3.drop 30++n4\n'
 s+=f'''theorem regroup : numeric={hashn}.message := by
  have step0 : [16,114]++n0++n1={hashn}.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3={hashn}.B01.input++n3.drop 30 := by rfl
  have step2 : rest2={hashn}.tail := by rfl
  have h0 : numeric={hashn}.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1={hashn}.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [{hashn}.message,{hashn}.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨{pos},by decide⟩))).map Fin.val={hashn}.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨{pos},by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨{pos},by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {{D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}}
      hash 2#usize (JFo_Opening.value ⟨{pos},by decide⟩)=ok (encodeState {ro}.value{i:03}) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨{pos},by decide⟩)=
    ({{D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨{pos},by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JＦp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨{pos},by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,{hashn}.checked]
  rfl
#print axioms source
end AspisR1.{name}
end
'''.replace('JＦp','JFp')
 files[R/'lean'/(name+'.lean')]=s
paired={}
for pos in range(10,22,4):
 texts=[files[R/'lean'/f'JGc_TX2_M2Leaf{k:02}.lean'] for k in range(pos,pos+4)]
 imports=sorted({line for text in texts for line in text.splitlines() if line.startswith('import ')})
 paired[R/'lean'/f'JGc_TX2_M2LeafSources{pos:02}.lean']='\n'.join(imports)+'\n'+''.join(text[text.index('set_option'):] for text in texts)
files=paired
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('leaf source generator:',len(files),'modules, four leaves/module, five32-byte windows/leaf')
