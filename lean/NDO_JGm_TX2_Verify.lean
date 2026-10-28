import NDO_JGc_TX2_M2Root
import NDO_JGf_TX2_M0Root
import NDO_JGh_TX2_M1Root
import NDO_JGm_TX2_Levels0
import NDO_JGm_TX2_Levels1
import NDO_JGm_TX2_Levels2
import NDO_JGm_TX2_Valid
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Verify0
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0 JGm_TX2_Supplied.nodes1 JGm_TX2_Supplied.nodes2

def output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (s : reference.Scratch) : reference.Scratch := Classical.choose (JGm_TX2_Levels0.on_scratch D hash s)

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGf_TX2_M0Root.retainedRoot) (JGk_TX2_Scratch0.s12 s) JGm_TX2_Supplied.nodes0=
        ok (true,output D hash s) := by
  obtain ⟨levels,view⟩ := Classical.choose_spec (JGm_TX2_Levels0.on_scratch D hash s)
  have n : (output D hash s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output D hash s).«at»=5216#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output D hash s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output D hash s).val 0#usize=ok (encodeState JGf_TX2_M0Roots.value185) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [JGf_TX2_M0Root.value_eq] at value
  have reset : {JGk_TX2_Scratch0.s12 s with «at»:=0#usize}=JGk_TX2_Scratch0.s12 s := rfl
  have len : Slice.len JGm_TX2_Supplied.nodes0=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length0
  have modulo : 5216#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=5216#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  have valid : reference.valid_indices (JGk_TX2_Scratch0.s12 s).idx (JGk_TX2_Scratch0.s12 s).n 0#usize=ok true := JGm_TX2_Valid0.on_scratch s
  rw [reference.verify_owned,
    if_neg (by change ¬12#usize=0#usize;decide),
    if_neg (by change ¬12#usize>16#usize;decide),valid]
  simp only [bind_tc_ok,Bool.true_eq,if_true,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,if_false]
  rw [reset,levels]
  simp only [bind_tc_ok]
  change (do if (output D hash s).n=1#usize then
               let i ← Array.index_usize (output D hash s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output D hash s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState JGf_TX2_M0Root.retainedRoot)
                 if b then ok (decide ((output D hash s).«at»=5216#usize),output D hash s)
                 else ok (false,output D hash s)
               else ok (false,output D hash s)
             else ok (false,output D hash s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.JGm_TX2_Verify0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Verify1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0 JGm_TX2_Supplied.nodes1 JGm_TX2_Supplied.nodes2

def output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (s : reference.Scratch) : reference.Scratch := Classical.choose (JGm_TX2_Levels1.on_scratch D hash s)

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGh_TX2_M1Root.retainedRoot) (JGk_TX2_Scratch1.s12 s) JGm_TX2_Supplied.nodes1=
        ok (true,output D hash s) := by
  obtain ⟨levels,view⟩ := Classical.choose_spec (JGm_TX2_Levels1.on_scratch D hash s)
  have n : (output D hash s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output D hash s).«at»=5216#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output D hash s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output D hash s).val 0#usize=ok (encodeState JGh_TX2_M1Roots.value185) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [JGh_TX2_M1Root.value_eq] at value
  have reset : {JGk_TX2_Scratch1.s12 s with «at»:=0#usize}=JGk_TX2_Scratch1.s12 s := rfl
  have len : Slice.len JGm_TX2_Supplied.nodes1=5216#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length1
  have modulo : 5216#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=5216#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  have valid : reference.valid_indices (JGk_TX2_Scratch1.s12 s).idx (JGk_TX2_Scratch1.s12 s).n 0#usize=ok true := JGm_TX2_Valid1.on_scratch s
  rw [reference.verify_owned,
    if_neg (by change ¬12#usize=0#usize;decide),
    if_neg (by change ¬12#usize>16#usize;decide),valid]
  simp only [bind_tc_ok,Bool.true_eq,if_true,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,if_false]
  rw [reset,levels]
  simp only [bind_tc_ok]
  change (do if (output D hash s).n=1#usize then
               let i ← Array.index_usize (output D hash s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output D hash s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState JGh_TX2_M1Root.retainedRoot)
                 if b then ok (decide ((output D hash s).«at»=5216#usize),output D hash s)
                 else ok (false,output D hash s)
               else ok (false,output D hash s)
             else ok (false,output D hash s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.JGm_TX2_Verify1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Verify2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGm_TX2_Supplied.nodes0 JGm_TX2_Supplied.nodes1 JGm_TX2_Supplied.nodes2

def output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (s : reference.Scratch) : reference.Scratch := Classical.choose (JGm_TX2_Levels2.on_scratch D hash s)

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGc_TX2_M2Root.retainedRoot) (JGk_TX2_Scratch2.s12 s) JGm_TX2_Supplied.nodes2=
        ok (true,output D hash s) := by
  obtain ⟨levels,view⟩ := Classical.choose_spec (JGm_TX2_Levels2.on_scratch D hash s)
  have n : (output D hash s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output D hash s).«at»=4512#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output D hash s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output D hash s).val 0#usize=ok (encodeState JGc_TX2_M2Roots.value163) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [JGc_TX2_M2Root.value_eq] at value
  have reset : {JGk_TX2_Scratch2.s12 s with «at»:=0#usize}=JGk_TX2_Scratch2.s12 s := rfl
  have len : Slice.len JGm_TX2_Supplied.nodes2=4512#usize := UScalar.eq_of_val_eq JGm_TX2_Supplied.length2
  have modulo : 4512#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=4512#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  have valid : reference.valid_indices (JGk_TX2_Scratch2.s12 s).idx (JGk_TX2_Scratch2.s12 s).n 0#usize=ok true := JGm_TX2_Valid2.on_scratch s
  rw [reference.verify_owned,
    if_neg (by change ¬12#usize=0#usize;decide),
    if_neg (by change ¬12#usize>16#usize;decide),valid]
  simp only [bind_tc_ok,Bool.true_eq,if_true,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,if_false]
  rw [reset,levels]
  simp only [bind_tc_ok]
  change (do if (output D hash s).n=1#usize then
               let i ← Array.index_usize (output D hash s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output D hash s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState JGc_TX2_M2Root.retainedRoot)
                 if b then ok (decide ((output D hash s).«at»=4512#usize),output D hash s)
                 else ok (false,output D hash s)
               else ok (false,output D hash s)
             else ok (false,output D hash s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.JGm_TX2_Verify2
end
