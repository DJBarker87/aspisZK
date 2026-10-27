from pathlib import Path
R=Path(__file__).resolve().parents[2]
for t,pre,n in [(0,'JGf','185'),(1,'JGh','185'),(2,'JGc','163')]:
 ns=f'JGm_TX2_Verify{t}';c=5216 if t<2 else 4512
 s=f'''import JGm_TX2_Levels{t}
import JGm_TX2_Valid{t}
import {pre}_TX2_M{t}Root
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge

def output (s : reference.Scratch) := JGm_TX2_Levels{t}.s18 (JGk_TX2_Scratch{t}.s12 s)

theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState {pre}_TX2_M{t}Root.retainedRoot) (JGk_TX2_Scratch{t}.s12 s) JGm_TX2_Supplied.nodes{t}=
        ok (true,output s) := by
  obtain ⟨levels,view⟩ := JGm_TX2_Levels{t}.on_scratch D hash s
  have n : (output s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output s).«at»={c}#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output s).val 0#usize=ok (encodeState {pre}_TX2_M{t}Roots.value{n}) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [{pre}_TX2_M{t}Root.value_eq] at value
  have reset : {{JGk_TX2_Scratch{t}.s12 s with «at»:=0#usize}}=JGk_TX2_Scratch{t}.s12 s := rfl
  have len : Slice.len JGm_TX2_Supplied.nodes{t}={c}#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length{t}
  have modulo : {c}#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:={c}#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  rw [reference.verify_owned]
  simp only [show (JGk_TX2_Scratch{t}.s12 s).n=12#usize from rfl,
    show (12#usize=0#usize)=False from propext (by decide),
    show (12#usize>16#usize)=False from propext (by decide),if_false,if_true,Bool.true_eq,
    JGm_TX2_Valid{t}.on_scratch,bind_tc_ok,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,reset,levels]
  change (do if (output s).n=1#usize then
               let i ← Array.index_usize (output s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState {pre}_TX2_M{t}Root.retainedRoot)
                 if b then ok ((output s).«at»=Slice.len JGm_TX2_Supplied.nodes{t},output s)
                 else ok (false,output s)
               else ok (false,output s)
             else ok (false,output s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.{ns}
end
'''
 (R/f'lean/{ns}.lean').write_text(s)
print('Generated native owned verifier compositions')
