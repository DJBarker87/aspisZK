import JGu_Level2_00
import JGu_Level2_01
import JGu_Level2_02
import JGu_Level2_03
import JGu_Level2_04
import JGu_Level2_05
import JGu_Level2_06
import JGu_Level2_07
import JGu_Level2_08
import JGu_Level2_09
import JGu_Level2_10
import JGu_Level2_11
import JGu_Level2_12
import JGu_Level2_13
import JGu_Level2_14
import JGu_Level2_15
import JGu_Level2_16
import JGu_Level2_17
import JGm_TX2_HeightTools
import JGu_Initial2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Levels2
open Aeneas Aeneas.Std Result MultiproofConeRef

def PhaseView (height : Nat) (s : reference.Scratch) : Prop := match height with
  | 0 => JGm_TX2_View.View s JGu_Level2_00.indices00 JGu_Level2_00.values00 0
  | 1 => JGm_TX2_View.View s JGu_Level2_01.indices00 JGu_Level2_01.values00 320
  | 2 => JGm_TX2_View.View s JGu_Level2_02.indices00 JGu_Level2_02.values00 640
  | 3 => JGm_TX2_View.View s JGu_Level2_03.indices00 JGu_Level2_03.values00 960
  | 4 => JGm_TX2_View.View s JGu_Level2_04.indices00 JGu_Level2_04.values00 1280
  | 5 => JGm_TX2_View.View s JGu_Level2_05.indices00 JGu_Level2_05.values00 1600
  | 6 => JGm_TX2_View.View s JGu_Level2_06.indices00 JGu_Level2_06.values00 1920
  | 7 => JGm_TX2_View.View s JGu_Level2_07.indices00 JGu_Level2_07.values00 2240
  | 8 => JGm_TX2_View.View s JGu_Level2_08.indices00 JGu_Level2_08.values00 2560
  | 9 => JGm_TX2_View.View s JGu_Level2_09.indices00 JGu_Level2_09.values00 2880
  | 10 => JGm_TX2_View.View s JGu_Level2_10.indices00 JGu_Level2_10.values00 3200
  | 11 => JGm_TX2_View.View s JGu_Level2_11.indices00 JGu_Level2_11.values00 3456
  | 12 => JGm_TX2_View.View s JGu_Level2_12.indices00 JGu_Level2_12.values00 3616
  | 13 => JGm_TX2_View.View s JGu_Level2_13.indices00 JGu_Level2_13.values00 3712
  | 14 => JGm_TX2_View.View s JGu_Level2_14.indices00 JGu_Level2_14.values00 3744
  | 15 => JGm_TX2_View.View s JGu_Level2_15.indices00 JGu_Level2_15.values00 3776
  | 16 => JGm_TX2_View.View s JGu_Level2_16.indices00 JGu_Level2_16.values00 3776
  | 17 => JGm_TX2_View.View s JGu_Level2_17.indices00 JGu_Level2_17.values00 3808
  | 18 => JGm_TX2_View.View s JGu_Level2_17.indicesOut JGu_Level2_17.valuesOut 3840
  | _ => False

theorem step {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (h : Nat) (bound : h<18) (s : reference.Scratch) (view : PhaseView h s) :
    ∃ out, reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done out) ∧ PhaseView (h+1) out := by
  interval_cases h
  · exact ⟨_,JGu_Level2_00.source D hash s view⟩
  · exact ⟨_,JGu_Level2_01.source D hash s view⟩
  · exact ⟨_,JGu_Level2_02.source D hash s view⟩
  · exact ⟨_,JGu_Level2_03.source D hash s view⟩
  · exact ⟨_,JGu_Level2_04.source D hash s view⟩
  · exact ⟨_,JGu_Level2_05.source D hash s view⟩
  · exact ⟨_,JGu_Level2_06.source D hash s view⟩
  · exact ⟨_,JGu_Level2_07.source D hash s view⟩
  · exact ⟨_,JGu_Level2_08.source D hash s view⟩
  · exact ⟨_,JGu_Level2_09.source D hash s view⟩
  · exact ⟨_,JGu_Level2_10.source D hash s view⟩
  · exact ⟨_,JGu_Level2_11.source D hash s view⟩
  · exact ⟨_,JGu_Level2_12.source D hash s view⟩
  · exact ⟨_,JGu_Level2_13.source D hash s view⟩
  · exact ⟨_,JGu_Level2_14.source D hash s view⟩
  · exact ⟨_,JGu_Level2_15.source D hash s view⟩
  · exact ⟨_,JGu_Level2_16.source D hash s view⟩
  · exact ⟨_,JGu_Level2_17.source D hash s view⟩
#print axioms step

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGu_Level2_00.indices00 JGu_Level2_00.values00 0) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGu_Supplied.nodes2 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGu_Level2_17.indicesOut JGu_Level2_17.valuesOut 3840 := by
  obtain ⟨out,run,last⟩ := JGm_TX2_HeightTools.compose (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGu_Supplied.nodes2 0#usize 0#usize) 18 PhaseView (step D hash) s view
  refine ⟨out,?_,last⟩
  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  exact run
#print axioms source

theorem on_scratch {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (JGu_Scratch2.s10 s) JGu_Supplied.nodes2 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGu_Level2_17.indicesOut JGu_Level2_17.valuesOut 3840 :=
  source D hash _ (JGu_Initial2.source s)
#print axioms on_scratch
end AspisR1.JGu_Levels2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Valid2
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGu_Level2_00.indices00 JGu_Level2_00.values00 0) :
    reference.valid_indices s.idx 10#usize 0#usize=ok true := by
  have r00 : Array.index_usize s.idx 0#usize=ok 16398#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 0#usize (by decide)
  have r01 : Array.index_usize s.idx 1#usize=ok 23374#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 1#usize (by decide)
  have r02 : Array.index_usize s.idx 2#usize=ok 36882#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 2#usize (by decide)
  have r03 : Array.index_usize s.idx 3#usize=ok 39953#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 3#usize (by decide)
  have r04 : Array.index_usize s.idx 4#usize=ok 45964#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 4#usize (by decide)
  have r05 : Array.index_usize s.idx 5#usize=ok 48079#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 5#usize (by decide)
  have r06 : Array.index_usize s.idx 6#usize=ok 48273#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 6#usize (by decide)
  have r07 : Array.index_usize s.idx 7#usize=ok 52342#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 7#usize (by decide)
  have r08 : Array.index_usize s.idx 8#usize=ok 54205#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 8#usize (by decide)
  have r09 : Array.index_usize s.idx 9#usize=ok 61474#u32 :=
    JGm_TX2_View.index s JGu_Level2_00.indices00 JGu_Level2_00.values00 0 view 9#usize (by decide)
  calc
    reference.valid_indices s.idx 10#usize 0#usize=reference.valid_indices s.idx 10#usize 1#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬0#usize≥10#usize),r00]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬16398#u32≥262144#u32)]
      rw [if_neg (by decide : ¬0#usize>0#usize)]
      rw [JGm_TX2_Scalar.add 0#usize 1#usize 1#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 2#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬1#usize≥10#usize),r01]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬23374#u32≥262144#u32)]
      rw [if_pos (by decide : 1#usize>0#usize),JGm_TX2_Scalar.sub 1#usize 1#usize 0#usize (by decide) rfl,bind_tc_ok,r00,bind_tc_ok,
        if_neg (by decide : ¬16398#u32≥23374#u32)]
      rw [JGm_TX2_Scalar.add 1#usize 1#usize 2#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 3#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬2#usize≥10#usize),r02]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬36882#u32≥262144#u32)]
      rw [if_pos (by decide : 2#usize>0#usize),JGm_TX2_Scalar.sub 2#usize 1#usize 1#usize (by decide) rfl,bind_tc_ok,r01,bind_tc_ok,
        if_neg (by decide : ¬23374#u32≥36882#u32)]
      rw [JGm_TX2_Scalar.add 2#usize 1#usize 3#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 4#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬3#usize≥10#usize),r03]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬39953#u32≥262144#u32)]
      rw [if_pos (by decide : 3#usize>0#usize),JGm_TX2_Scalar.sub 3#usize 1#usize 2#usize (by decide) rfl,bind_tc_ok,r02,bind_tc_ok,
        if_neg (by decide : ¬36882#u32≥39953#u32)]
      rw [JGm_TX2_Scalar.add 3#usize 1#usize 4#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 5#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬4#usize≥10#usize),r04]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬45964#u32≥262144#u32)]
      rw [if_pos (by decide : 4#usize>0#usize),JGm_TX2_Scalar.sub 4#usize 1#usize 3#usize (by decide) rfl,bind_tc_ok,r03,bind_tc_ok,
        if_neg (by decide : ¬39953#u32≥45964#u32)]
      rw [JGm_TX2_Scalar.add 4#usize 1#usize 5#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 6#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬5#usize≥10#usize),r05]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬48079#u32≥262144#u32)]
      rw [if_pos (by decide : 5#usize>0#usize),JGm_TX2_Scalar.sub 5#usize 1#usize 4#usize (by decide) rfl,bind_tc_ok,r04,bind_tc_ok,
        if_neg (by decide : ¬45964#u32≥48079#u32)]
      rw [JGm_TX2_Scalar.add 5#usize 1#usize 6#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 7#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬6#usize≥10#usize),r06]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬48273#u32≥262144#u32)]
      rw [if_pos (by decide : 6#usize>0#usize),JGm_TX2_Scalar.sub 6#usize 1#usize 5#usize (by decide) rfl,bind_tc_ok,r05,bind_tc_ok,
        if_neg (by decide : ¬48079#u32≥48273#u32)]
      rw [JGm_TX2_Scalar.add 6#usize 1#usize 7#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 8#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬7#usize≥10#usize),r07]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬52342#u32≥262144#u32)]
      rw [if_pos (by decide : 7#usize>0#usize),JGm_TX2_Scalar.sub 7#usize 1#usize 6#usize (by decide) rfl,bind_tc_ok,r06,bind_tc_ok,
        if_neg (by decide : ¬48273#u32≥52342#u32)]
      rw [JGm_TX2_Scalar.add 7#usize 1#usize 8#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 9#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬8#usize≥10#usize),r08]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬54205#u32≥262144#u32)]
      rw [if_pos (by decide : 8#usize>0#usize),JGm_TX2_Scalar.sub 8#usize 1#usize 7#usize (by decide) rfl,bind_tc_ok,r07,bind_tc_ok,
        if_neg (by decide : ¬52342#u32≥54205#u32)]
      rw [JGm_TX2_Scalar.add 8#usize 1#usize 9#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 10#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬9#usize≥10#usize),r09]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬61474#u32≥262144#u32)]
      rw [if_pos (by decide : 9#usize>0#usize),JGm_TX2_Scalar.sub 9#usize 1#usize 8#usize (by decide) rfl,bind_tc_ok,r08,bind_tc_ok,
        if_neg (by decide : ¬54205#u32≥61474#u32)]
      rw [JGm_TX2_Scalar.add 9#usize 1#usize 10#usize rfl]
      rfl
    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 10#usize≥10#usize)]
#print axioms source
theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JGu_Scratch2.s10 s).idx 10#usize 0#usize=ok true :=
  source _ (JGu_Initial2.source s)
#print axioms on_scratch
end AspisR1.JGu_Valid2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Verify2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2 JGu_Supplied.nodes0 JGu_Supplied.nodes1 JGu_Supplied.nodes2

def output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (s : reference.Scratch) : reference.Scratch := Classical.choose (JGu_Levels2.on_scratch D hash s)

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JGr_M2Root.retainedRoot) (JGu_Scratch2.s10 s) JGu_Supplied.nodes2=
        ok (true,output D hash s) := by
  obtain ⟨levels,view⟩ := Classical.choose_spec (JGu_Levels2.on_scratch D hash s)
  have n : (output D hash s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output D hash s).«at»=4510#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output D hash s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output D hash s).val 0#usize=ok (encodeState JGr_M2Roots.value163) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [JGr_M2Root.value_eq] at value
  have reset : {JGu_Scratch2.s10 s with «at»:=0#usize}=JGu_Scratch2.s10 s := rfl
  have len : Slice.len JGu_Supplied.nodes2=4510#usize := UScalar.eq_of_val_eq JGu_Supplied.length2
  have modulo : 4510#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=4510#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  have valid : reference.valid_indices (JGu_Scratch2.s10 s).idx (JGu_Scratch2.s10 s).n 0#usize=ok true := JGu_Valid2.on_scratch s
  rw [reference.verify_owned,
    if_neg (by change ¬10#usize=0#usize;decide),
    if_neg (by change ¬10#usize>16#usize;decide),valid]
  simp only [bind_tc_ok,Bool.true_eq,if_true,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,if_false]
  rw [reset,levels]
  simp only [bind_tc_ok]
  change (do if (output D hash s).n=1#usize then
               let i ← Array.index_usize (output D hash s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output D hash s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState JGr_M2Root.retainedRoot)
                 if b then ok (decide ((output D hash s).«at»=4510#usize),output D hash s)
                 else ok (false,output D hash s)
               else ok (false,output D hash s)
             else ok (false,output D hash s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.JGu_Verify2
end
