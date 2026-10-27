from pathlib import Path
import json,re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
data=json.loads((R/'evidence/joint-fixture24-20261027/JGr_MERKLE_PREFLIGHT.json').read_text())['trees']
# Byte selection reduces only the selected physical 32-byte cell, never SHA.
reductions='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
def selected(off,n,goal):
 s=f'  change ((JFx_NativeBytes.proof.val.drop {off}).take {n})={goal}\n'
 s+='  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,'+','.join(f'JFx_DataProof{x:02}.length' for x in range(15))+','+reductions+']\n'
 # only byte blocks intersecting the selected interval
 for x in range(off//4096,(off+n-1)//4096+1):
  f=R/f'lean/JFx_DataProof{x:02}.lean'; text=f.read_text()
  lengths=re.findall(r'theorem (c\d+_length)',text)
  s+=f'  simp only [JFx_DataProof{x:02}.bytes,'+','.join(f'JFx_DataProof{x:02}.{k}' for k in lengths)+','+reductions+']\n'
 s+='  rfl\n';return s
s='import JGm_TX2_Supplied\n'+''.join(f'import JGp_Slot{t}\n' for t in range(3))+'''set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Supplied
open Aeneas Aeneas.Std Result MultiproofConeRef
'''
for t,row in enumerate(data):
 count=row['consumed'];cap=[146,146,128][t]
 s+=f'''def nodes{t} : Slice U8 := JGm_TX2_Supplied.leading JGp_Slot{t}.value {32*count}#usize
theorem length{t} : nodes{t}.val.length={32*count} :=
  JGm_TX2_Supplied.size _ _ (by change ({32*count}:Nat)≤JGp_Slot{t}.value.val.length; have len : JGp_Slot{t}.value.val.length={32*cap} := JGp_Slot{t}.length; rw [len];decide)
#print axioms length{t}
'''
s+='end AspisR1.JGu_Supplied\nend\n'
(R/'lean/JGu_Supplied.lean').write_text(s)
# Reuse the native-level proof emitter; replace only fixture coordinates and physical reads.
s=(R/'evidence/fixture-tx2m-20261027/JGm_native_levels.py').read_text()
s=s.replace("[(0,'JGf'),(1,'JGh'),(2,'JGc')]","[(0,'JGr'),(1,'JGr'),(2,'JGr')]")
s=s.replace("{pre}_TX2_M","{pre}_M").replace("glob(f'{pre}_M{t}Level*.lean')","glob(f'{pre}_M{t}Branch*.lean')")
start=s.index(' # physical supplied sibling');end=s.index(' # Actual frontier',start)
s=s[:start]+s[end:]
s=s.replace('count=163 if t<2 else 141','count=138 if t<2 else 120')
s=s.replace('JGm_TX2_Level','JGu_Level').replace('JGm_TX2_ParentCalls','JGu_ParentCalls')
s=s.replace('import JGm_TX2_Supplied','import JGu_Supplied').replace('JGm_TX2_Supplied.nodes','JGu_Supplied.nodes').replace('JGm_TX2_Supplied.length','JGu_Supplied.length')
s=s.replace('    st=siblings[before][1]','')
s=s.replace('    assert st.startswith(f"{pre}_M{t}Roots.siblingAt "),(t,h,before,st)','')
a=s.index('    have read := JGm_TX2_Supplied.source');b=s.index('  have selected{w:02}',a)
s=s[:a]+'''    unfold JGu_Supplied.nodes{t}
    rw [JGm_TX2_Supplied.sub_prefix JGp_Slot{t}.value {32*count}#usize {32*before}#usize {32*c}#usize (by decide) (by decide)]
    have phys : (MultiproofConeSlices.sub JGp_Slot{t}.value {32*before}#usize {32*c}#usize).val=
        (encodeState ({expected})).val := by
      change (((JFw_Frames.window {data[t]['slot_start']} {32*[146,146,128][t]}).val.drop {32*before}).take 32)=_
      rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
{select_body(data[t]['slot_start']+32*before,expected)}
    obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
      (MultiproofConeSlices.sub JGp_Slot{t}.value {32*before}#usize {32*c}#usize)
      (by rw [phys,(encodeState ({expected})).property];decide)
    have same : chunk=encodeState ({expected}) := by
      apply Subtype.ext
      rw [bytes,phys]
      exact List.take_of_length_le (by rw [(encodeState ({expected})).property];decide)
    exact same ▸ run
'''+s[b:]
# additional imports and reducibility barriers preserve the physical window until the isolated read.
s=s.replace('import JGk_TX2_SiblingLaws','import JGk_TX2_SiblingLaws\nimport JFw_Frames\nimport JFq_Range')
s=s.replace('JGu_Supplied.nodes{t}\n\'\'\'','JGu_Supplied.nodes{t}\n\'\'\'')
s=s.replace("'JGm_LEVEL_SHAPES.json'","'JGu_LEVEL_SHAPES.json'").replace("'JGm_LEVEL_MODULES.json'","'JGu_LEVEL_MODULES.json'")
def select_body(off,expected):
 body=selected(off,32,f'(encodeState ({expected})).val')
 return '\n'.join('    '+line for line in body.rstrip().splitlines())
if '--levels' in sys.argv:exec(compile(s,str(P/'JGu_levels_emitter'),'exec'),globals())
(P/'JGu_levels_generated.lean.txt').write_text(s)
