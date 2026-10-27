from pathlib import Path
R=Path(__file__).resolve().parents[2]
positions=[21,17,15,19,18,10,13,14,12,16,20,11]
values=[14297,21248,42158,55377,63860,132355,149624,166165,178080,179622,185637,218094]
for t in range(3):
 ns=f'JGk_TX2_Scratch{t}'
 s=f'''import JGk_TX2_ScratchKeys
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGk_TX2_ScratchKeys.keys JGk_TX2_NativeLeaves.value0 JGk_TX2_NativeLeaves.value1 JGc_TX2_RealLeaves.value

def s00 (s : reference.Scratch) : reference.Scratch := {{s with n:=0#usize,«at»:=0#usize}}
'''
 for i,(pos,index) in enumerate(zip(positions,values)):
  if t==2:index//=4
  digest=f'encodeState ({"JGk_TX2_NativeLeaves.value"+str(t) if t<2 else "JGc_TX2_RealLeaves.value"} ⟨{pos-10},by decide⟩)'
  old=f's{i:02} s';new=f's{i+1:02} s'
  s+=f'''def s{i+1:02} (s : reference.Scratch) : reference.Scratch :=
  JGk_TX2_LeafPush.push ({old}) {index}#u32 ({digest}) (by change ({i}:Nat)<16; decide)

theorem body{i:02} {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root {t}#usize hash 10#usize 12#usize {t+3}#usize (JGk_TX2_ScratchKeys.keys {t})
      ({old}).idx ({old}).val ({old}).n {i}#usize=
        ok (.cont (({new}).idx,({new}).val,({new}).n,{i+1}#usize)) := by
  have read := JGk_TX2_ScratchKeys.stream{t} {i}#usize {i} (by decide) rfl
  have native := JGk_TX2_LeafIteration.source{t} D hash ⟨{pos-10},by decide⟩
    {i}#usize (JGk_TX2_ScratchKeys.keys {t}) root ({old}) (by decide) (by change ({i}:Nat)<16; decide) read
  dsimp only [Fin.val_mk,Nat.reduceAdd] at native
  have member : {pos} ∈ OraclePortSelectedDraft.batchPositions 1 := by decide
  have decoded : Port4B_NativeLeaf.decodedIndex
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 {t} {pos})={index}#u32 := by
    apply UScalar.eq_of_val_eq
    exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 {t} {pos} member 10#usize rfl).1
  have fresh : ¬(0<({old}).n.val ∧ ({old}).idx.val[({old}).n.val-1]! = {index}#u32) := by
'''
  if i==0:s+='    intro h\n    exact (Nat.lt_irrefl 0) h.1\n'
  else:
   preindex=values[i-1]//4 if t==2 else values[i-1]
   prevdigest=f'encodeState ({"JGk_TX2_NativeLeaves.value"+str(t) if t<2 else "JGc_TX2_RealLeaves.value"} ⟨{positions[i-1]-10},by decide⟩)'
   s+=f'''    have last : ({old}).idx.val[({old}).n.val-1]! = {preindex}#u32 :=
      JGk_TX2_LeafPush.last (s{i-1:02} s) {preindex}#u32 ({prevdigest}) (by change ({i-1}:Nat)<16; decide)
    intro h
    exact (by decide : {preindex}#u32≠{index}#u32) (last.symm.trans h.2)
'''
  s+=f'''  rw [decoded,JGk_TX2_LeafPush.step ({old}) {index}#u32 ({digest}) (by change ({i}:Nat)<16; decide) fresh] at native
  have advance : Usize.wrapping_add {i}#usize 1#usize={i+1}#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment {i}#usize (by decide)
  simpa only [bind_tc_ok,Port4B_LeafStep.project,advance,s{i+1:02}] using native
#print axioms body{i:02}
'''
 s+=f'''theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root {t}#usize (s00 s).idx (s00 s).val hash 10#usize 12#usize {t+3}#usize
      (JGk_TX2_ScratchKeys.keys {t}) (s00 s).n 0#usize=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root {t}#usize (s12 s).idx (s12 s).val hash 10#usize 12#usize {t+3}#usize
      (JGk_TX2_ScratchKeys.keys {t}) (s12 s).n 12#usize := by
'''
 for i in range(12):
  head='  exact ' if i==0 else '    '
  term=f'JGk_TX2_ScratchKeys.advance_loop D hash root {t}#usize {t+3}#usize {i}#usize {i+1}#usize (s{i:02} s) (s{i+1:02} s) (body{i:02} D hash root s)'
  s+=head+'('+term+')'+('.trans (\n' if i<11 else ')'*11+'\n')
 s+=f'#print axioms source\nend AspisR1.{ns}\nend\n'
 (R/f'lean/{ns}.lean').write_text(s)
