import NDO_JGm_TX2_Initial
import NDO_JGm_TX2_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Valid0
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0) :
    reference.valid_indices s.idx 12#usize 0#usize=ok true := by
  have r00 : Array.index_usize s.idx 0#usize=ok 14297#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 0#usize (by decide)
  have r01 : Array.index_usize s.idx 1#usize=ok 21248#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 1#usize (by decide)
  have r02 : Array.index_usize s.idx 2#usize=ok 42158#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 2#usize (by decide)
  have r03 : Array.index_usize s.idx 3#usize=ok 55377#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 3#usize (by decide)
  have r04 : Array.index_usize s.idx 4#usize=ok 63860#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 4#usize (by decide)
  have r05 : Array.index_usize s.idx 5#usize=ok 132355#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 5#usize (by decide)
  have r06 : Array.index_usize s.idx 6#usize=ok 149624#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 6#usize (by decide)
  have r07 : Array.index_usize s.idx 7#usize=ok 166165#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 7#usize (by decide)
  have r08 : Array.index_usize s.idx 8#usize=ok 178080#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 8#usize (by decide)
  have r09 : Array.index_usize s.idx 9#usize=ok 179622#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 9#usize (by decide)
  have r10 : Array.index_usize s.idx 10#usize=ok 185637#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 10#usize (by decide)
  have r11 : Array.index_usize s.idx 11#usize=ok 218094#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 view 11#usize (by decide)
  calc
    reference.valid_indices s.idx 12#usize 0#usize=reference.valid_indices s.idx 12#usize 1#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬0#usize≥12#usize),r00]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬14297#u32≥262144#u32)]
      rw [if_neg (by decide : ¬0#usize>0#usize)]
      rw [JGm_TX2_Scalar.add 0#usize 1#usize 1#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 2#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬1#usize≥12#usize),r01]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬21248#u32≥262144#u32)]
      rw [if_pos (by decide : 1#usize>0#usize),JGm_TX2_Scalar.sub 1#usize 1#usize 0#usize (by decide) rfl,bind_tc_ok,r00,bind_tc_ok,
        if_neg (by decide : ¬14297#u32≥21248#u32)]
      rw [JGm_TX2_Scalar.add 1#usize 1#usize 2#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 3#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬2#usize≥12#usize),r02]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬42158#u32≥262144#u32)]
      rw [if_pos (by decide : 2#usize>0#usize),JGm_TX2_Scalar.sub 2#usize 1#usize 1#usize (by decide) rfl,bind_tc_ok,r01,bind_tc_ok,
        if_neg (by decide : ¬21248#u32≥42158#u32)]
      rw [JGm_TX2_Scalar.add 2#usize 1#usize 3#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 4#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬3#usize≥12#usize),r03]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬55377#u32≥262144#u32)]
      rw [if_pos (by decide : 3#usize>0#usize),JGm_TX2_Scalar.sub 3#usize 1#usize 2#usize (by decide) rfl,bind_tc_ok,r02,bind_tc_ok,
        if_neg (by decide : ¬42158#u32≥55377#u32)]
      rw [JGm_TX2_Scalar.add 3#usize 1#usize 4#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 5#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬4#usize≥12#usize),r04]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬63860#u32≥262144#u32)]
      rw [if_pos (by decide : 4#usize>0#usize),JGm_TX2_Scalar.sub 4#usize 1#usize 3#usize (by decide) rfl,bind_tc_ok,r03,bind_tc_ok,
        if_neg (by decide : ¬55377#u32≥63860#u32)]
      rw [JGm_TX2_Scalar.add 4#usize 1#usize 5#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 6#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬5#usize≥12#usize),r05]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬132355#u32≥262144#u32)]
      rw [if_pos (by decide : 5#usize>0#usize),JGm_TX2_Scalar.sub 5#usize 1#usize 4#usize (by decide) rfl,bind_tc_ok,r04,bind_tc_ok,
        if_neg (by decide : ¬63860#u32≥132355#u32)]
      rw [JGm_TX2_Scalar.add 5#usize 1#usize 6#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 7#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬6#usize≥12#usize),r06]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬149624#u32≥262144#u32)]
      rw [if_pos (by decide : 6#usize>0#usize),JGm_TX2_Scalar.sub 6#usize 1#usize 5#usize (by decide) rfl,bind_tc_ok,r05,bind_tc_ok,
        if_neg (by decide : ¬132355#u32≥149624#u32)]
      rw [JGm_TX2_Scalar.add 6#usize 1#usize 7#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 8#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬7#usize≥12#usize),r07]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬166165#u32≥262144#u32)]
      rw [if_pos (by decide : 7#usize>0#usize),JGm_TX2_Scalar.sub 7#usize 1#usize 6#usize (by decide) rfl,bind_tc_ok,r06,bind_tc_ok,
        if_neg (by decide : ¬149624#u32≥166165#u32)]
      rw [JGm_TX2_Scalar.add 7#usize 1#usize 8#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 9#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬8#usize≥12#usize),r08]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬178080#u32≥262144#u32)]
      rw [if_pos (by decide : 8#usize>0#usize),JGm_TX2_Scalar.sub 8#usize 1#usize 7#usize (by decide) rfl,bind_tc_ok,r07,bind_tc_ok,
        if_neg (by decide : ¬166165#u32≥178080#u32)]
      rw [JGm_TX2_Scalar.add 8#usize 1#usize 9#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 10#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬9#usize≥12#usize),r09]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬179622#u32≥262144#u32)]
      rw [if_pos (by decide : 9#usize>0#usize),JGm_TX2_Scalar.sub 9#usize 1#usize 8#usize (by decide) rfl,bind_tc_ok,r08,bind_tc_ok,
        if_neg (by decide : ¬178080#u32≥179622#u32)]
      rw [JGm_TX2_Scalar.add 9#usize 1#usize 10#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 11#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬10#usize≥12#usize),r10]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬185637#u32≥262144#u32)]
      rw [if_pos (by decide : 10#usize>0#usize),JGm_TX2_Scalar.sub 10#usize 1#usize 9#usize (by decide) rfl,bind_tc_ok,r09,bind_tc_ok,
        if_neg (by decide : ¬179622#u32≥185637#u32)]
      rw [JGm_TX2_Scalar.add 10#usize 1#usize 11#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 12#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬11#usize≥12#usize),r11]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬218094#u32≥262144#u32)]
      rw [if_pos (by decide : 11#usize>0#usize),JGm_TX2_Scalar.sub 11#usize 1#usize 10#usize (by decide) rfl,bind_tc_ok,r10,bind_tc_ok,
        if_neg (by decide : ¬185637#u32≥218094#u32)]
      rw [JGm_TX2_Scalar.add 11#usize 1#usize 12#usize rfl]
      rfl
    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 12#usize≥12#usize)]
#print axioms source
theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JGk_TX2_Scratch0.s12 s).idx 12#usize 0#usize=ok true :=
  source _ (JGm_TX2_Initial0.source s)
#print axioms on_scratch
end AspisR1.JGm_TX2_Valid0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Valid1
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0) :
    reference.valid_indices s.idx 12#usize 0#usize=ok true := by
  have r00 : Array.index_usize s.idx 0#usize=ok 14297#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 0#usize (by decide)
  have r01 : Array.index_usize s.idx 1#usize=ok 21248#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 1#usize (by decide)
  have r02 : Array.index_usize s.idx 2#usize=ok 42158#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 2#usize (by decide)
  have r03 : Array.index_usize s.idx 3#usize=ok 55377#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 3#usize (by decide)
  have r04 : Array.index_usize s.idx 4#usize=ok 63860#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 4#usize (by decide)
  have r05 : Array.index_usize s.idx 5#usize=ok 132355#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 5#usize (by decide)
  have r06 : Array.index_usize s.idx 6#usize=ok 149624#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 6#usize (by decide)
  have r07 : Array.index_usize s.idx 7#usize=ok 166165#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 7#usize (by decide)
  have r08 : Array.index_usize s.idx 8#usize=ok 178080#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 8#usize (by decide)
  have r09 : Array.index_usize s.idx 9#usize=ok 179622#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 9#usize (by decide)
  have r10 : Array.index_usize s.idx 10#usize=ok 185637#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 10#usize (by decide)
  have r11 : Array.index_usize s.idx 11#usize=ok 218094#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 view 11#usize (by decide)
  calc
    reference.valid_indices s.idx 12#usize 0#usize=reference.valid_indices s.idx 12#usize 1#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬0#usize≥12#usize),r00]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬14297#u32≥262144#u32)]
      rw [if_neg (by decide : ¬0#usize>0#usize)]
      rw [JGm_TX2_Scalar.add 0#usize 1#usize 1#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 2#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬1#usize≥12#usize),r01]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬21248#u32≥262144#u32)]
      rw [if_pos (by decide : 1#usize>0#usize),JGm_TX2_Scalar.sub 1#usize 1#usize 0#usize (by decide) rfl,bind_tc_ok,r00,bind_tc_ok,
        if_neg (by decide : ¬14297#u32≥21248#u32)]
      rw [JGm_TX2_Scalar.add 1#usize 1#usize 2#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 3#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬2#usize≥12#usize),r02]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬42158#u32≥262144#u32)]
      rw [if_pos (by decide : 2#usize>0#usize),JGm_TX2_Scalar.sub 2#usize 1#usize 1#usize (by decide) rfl,bind_tc_ok,r01,bind_tc_ok,
        if_neg (by decide : ¬21248#u32≥42158#u32)]
      rw [JGm_TX2_Scalar.add 2#usize 1#usize 3#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 4#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬3#usize≥12#usize),r03]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬55377#u32≥262144#u32)]
      rw [if_pos (by decide : 3#usize>0#usize),JGm_TX2_Scalar.sub 3#usize 1#usize 2#usize (by decide) rfl,bind_tc_ok,r02,bind_tc_ok,
        if_neg (by decide : ¬42158#u32≥55377#u32)]
      rw [JGm_TX2_Scalar.add 3#usize 1#usize 4#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 5#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬4#usize≥12#usize),r04]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬63860#u32≥262144#u32)]
      rw [if_pos (by decide : 4#usize>0#usize),JGm_TX2_Scalar.sub 4#usize 1#usize 3#usize (by decide) rfl,bind_tc_ok,r03,bind_tc_ok,
        if_neg (by decide : ¬55377#u32≥63860#u32)]
      rw [JGm_TX2_Scalar.add 4#usize 1#usize 5#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 6#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬5#usize≥12#usize),r05]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬132355#u32≥262144#u32)]
      rw [if_pos (by decide : 5#usize>0#usize),JGm_TX2_Scalar.sub 5#usize 1#usize 4#usize (by decide) rfl,bind_tc_ok,r04,bind_tc_ok,
        if_neg (by decide : ¬63860#u32≥132355#u32)]
      rw [JGm_TX2_Scalar.add 5#usize 1#usize 6#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 7#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬6#usize≥12#usize),r06]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬149624#u32≥262144#u32)]
      rw [if_pos (by decide : 6#usize>0#usize),JGm_TX2_Scalar.sub 6#usize 1#usize 5#usize (by decide) rfl,bind_tc_ok,r05,bind_tc_ok,
        if_neg (by decide : ¬132355#u32≥149624#u32)]
      rw [JGm_TX2_Scalar.add 6#usize 1#usize 7#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 8#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬7#usize≥12#usize),r07]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬166165#u32≥262144#u32)]
      rw [if_pos (by decide : 7#usize>0#usize),JGm_TX2_Scalar.sub 7#usize 1#usize 6#usize (by decide) rfl,bind_tc_ok,r06,bind_tc_ok,
        if_neg (by decide : ¬149624#u32≥166165#u32)]
      rw [JGm_TX2_Scalar.add 7#usize 1#usize 8#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 9#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬8#usize≥12#usize),r08]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬178080#u32≥262144#u32)]
      rw [if_pos (by decide : 8#usize>0#usize),JGm_TX2_Scalar.sub 8#usize 1#usize 7#usize (by decide) rfl,bind_tc_ok,r07,bind_tc_ok,
        if_neg (by decide : ¬166165#u32≥178080#u32)]
      rw [JGm_TX2_Scalar.add 8#usize 1#usize 9#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 10#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬9#usize≥12#usize),r09]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬179622#u32≥262144#u32)]
      rw [if_pos (by decide : 9#usize>0#usize),JGm_TX2_Scalar.sub 9#usize 1#usize 8#usize (by decide) rfl,bind_tc_ok,r08,bind_tc_ok,
        if_neg (by decide : ¬178080#u32≥179622#u32)]
      rw [JGm_TX2_Scalar.add 9#usize 1#usize 10#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 11#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬10#usize≥12#usize),r10]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬185637#u32≥262144#u32)]
      rw [if_pos (by decide : 10#usize>0#usize),JGm_TX2_Scalar.sub 10#usize 1#usize 9#usize (by decide) rfl,bind_tc_ok,r09,bind_tc_ok,
        if_neg (by decide : ¬179622#u32≥185637#u32)]
      rw [JGm_TX2_Scalar.add 10#usize 1#usize 11#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 12#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬11#usize≥12#usize),r11]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬218094#u32≥262144#u32)]
      rw [if_pos (by decide : 11#usize>0#usize),JGm_TX2_Scalar.sub 11#usize 1#usize 10#usize (by decide) rfl,bind_tc_ok,r10,bind_tc_ok,
        if_neg (by decide : ¬185637#u32≥218094#u32)]
      rw [JGm_TX2_Scalar.add 11#usize 1#usize 12#usize rfl]
      rfl
    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 12#usize≥12#usize)]
#print axioms source
theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JGk_TX2_Scratch1.s12 s).idx 12#usize 0#usize=ok true :=
  source _ (JGm_TX2_Initial1.source s)
#print axioms on_scratch
end AspisR1.JGm_TX2_Valid1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Valid2
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0) :
    reference.valid_indices s.idx 12#usize 0#usize=ok true := by
  have r00 : Array.index_usize s.idx 0#usize=ok 3574#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 0#usize (by decide)
  have r01 : Array.index_usize s.idx 1#usize=ok 5312#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 1#usize (by decide)
  have r02 : Array.index_usize s.idx 2#usize=ok 10539#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 2#usize (by decide)
  have r03 : Array.index_usize s.idx 3#usize=ok 13844#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 3#usize (by decide)
  have r04 : Array.index_usize s.idx 4#usize=ok 15965#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 4#usize (by decide)
  have r05 : Array.index_usize s.idx 5#usize=ok 33088#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 5#usize (by decide)
  have r06 : Array.index_usize s.idx 6#usize=ok 37406#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 6#usize (by decide)
  have r07 : Array.index_usize s.idx 7#usize=ok 41541#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 7#usize (by decide)
  have r08 : Array.index_usize s.idx 8#usize=ok 44520#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 8#usize (by decide)
  have r09 : Array.index_usize s.idx 9#usize=ok 44905#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 9#usize (by decide)
  have r10 : Array.index_usize s.idx 10#usize=ok 46409#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 10#usize (by decide)
  have r11 : Array.index_usize s.idx 11#usize=ok 54523#u32 :=
    JGm_TX2_View.index s JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 view 11#usize (by decide)
  calc
    reference.valid_indices s.idx 12#usize 0#usize=reference.valid_indices s.idx 12#usize 1#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬0#usize≥12#usize),r00]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬3574#u32≥262144#u32)]
      rw [if_neg (by decide : ¬0#usize>0#usize)]
      rw [JGm_TX2_Scalar.add 0#usize 1#usize 1#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 2#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬1#usize≥12#usize),r01]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬5312#u32≥262144#u32)]
      rw [if_pos (by decide : 1#usize>0#usize),JGm_TX2_Scalar.sub 1#usize 1#usize 0#usize (by decide) rfl,bind_tc_ok,r00,bind_tc_ok,
        if_neg (by decide : ¬3574#u32≥5312#u32)]
      rw [JGm_TX2_Scalar.add 1#usize 1#usize 2#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 3#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬2#usize≥12#usize),r02]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬10539#u32≥262144#u32)]
      rw [if_pos (by decide : 2#usize>0#usize),JGm_TX2_Scalar.sub 2#usize 1#usize 1#usize (by decide) rfl,bind_tc_ok,r01,bind_tc_ok,
        if_neg (by decide : ¬5312#u32≥10539#u32)]
      rw [JGm_TX2_Scalar.add 2#usize 1#usize 3#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 4#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬3#usize≥12#usize),r03]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬13844#u32≥262144#u32)]
      rw [if_pos (by decide : 3#usize>0#usize),JGm_TX2_Scalar.sub 3#usize 1#usize 2#usize (by decide) rfl,bind_tc_ok,r02,bind_tc_ok,
        if_neg (by decide : ¬10539#u32≥13844#u32)]
      rw [JGm_TX2_Scalar.add 3#usize 1#usize 4#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 5#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬4#usize≥12#usize),r04]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬15965#u32≥262144#u32)]
      rw [if_pos (by decide : 4#usize>0#usize),JGm_TX2_Scalar.sub 4#usize 1#usize 3#usize (by decide) rfl,bind_tc_ok,r03,bind_tc_ok,
        if_neg (by decide : ¬13844#u32≥15965#u32)]
      rw [JGm_TX2_Scalar.add 4#usize 1#usize 5#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 6#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬5#usize≥12#usize),r05]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬33088#u32≥262144#u32)]
      rw [if_pos (by decide : 5#usize>0#usize),JGm_TX2_Scalar.sub 5#usize 1#usize 4#usize (by decide) rfl,bind_tc_ok,r04,bind_tc_ok,
        if_neg (by decide : ¬15965#u32≥33088#u32)]
      rw [JGm_TX2_Scalar.add 5#usize 1#usize 6#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 7#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬6#usize≥12#usize),r06]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬37406#u32≥262144#u32)]
      rw [if_pos (by decide : 6#usize>0#usize),JGm_TX2_Scalar.sub 6#usize 1#usize 5#usize (by decide) rfl,bind_tc_ok,r05,bind_tc_ok,
        if_neg (by decide : ¬33088#u32≥37406#u32)]
      rw [JGm_TX2_Scalar.add 6#usize 1#usize 7#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 8#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬7#usize≥12#usize),r07]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬41541#u32≥262144#u32)]
      rw [if_pos (by decide : 7#usize>0#usize),JGm_TX2_Scalar.sub 7#usize 1#usize 6#usize (by decide) rfl,bind_tc_ok,r06,bind_tc_ok,
        if_neg (by decide : ¬37406#u32≥41541#u32)]
      rw [JGm_TX2_Scalar.add 7#usize 1#usize 8#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 9#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬8#usize≥12#usize),r08]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬44520#u32≥262144#u32)]
      rw [if_pos (by decide : 8#usize>0#usize),JGm_TX2_Scalar.sub 8#usize 1#usize 7#usize (by decide) rfl,bind_tc_ok,r07,bind_tc_ok,
        if_neg (by decide : ¬41541#u32≥44520#u32)]
      rw [JGm_TX2_Scalar.add 8#usize 1#usize 9#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 10#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬9#usize≥12#usize),r09]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬44905#u32≥262144#u32)]
      rw [if_pos (by decide : 9#usize>0#usize),JGm_TX2_Scalar.sub 9#usize 1#usize 8#usize (by decide) rfl,bind_tc_ok,r08,bind_tc_ok,
        if_neg (by decide : ¬44520#u32≥44905#u32)]
      rw [JGm_TX2_Scalar.add 9#usize 1#usize 10#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 11#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬10#usize≥12#usize),r10]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬46409#u32≥262144#u32)]
      rw [if_pos (by decide : 10#usize>0#usize),JGm_TX2_Scalar.sub 10#usize 1#usize 9#usize (by decide) rfl,bind_tc_ok,r09,bind_tc_ok,
        if_neg (by decide : ¬44905#u32≥46409#u32)]
      rw [JGm_TX2_Scalar.add 10#usize 1#usize 11#usize rfl]
      rfl
    _=reference.valid_indices s.idx 12#usize 12#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬11#usize≥12#usize),r11]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬54523#u32≥262144#u32)]
      rw [if_pos (by decide : 11#usize>0#usize),JGm_TX2_Scalar.sub 11#usize 1#usize 10#usize (by decide) rfl,bind_tc_ok,r10,bind_tc_ok,
        if_neg (by decide : ¬46409#u32≥54523#u32)]
      rw [JGm_TX2_Scalar.add 11#usize 1#usize 12#usize rfl]
      rfl
    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 12#usize≥12#usize)]
#print axioms source
theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JGk_TX2_Scratch2.s12 s).idx 12#usize 0#usize=ok true :=
  source _ (JGm_TX2_Initial2.source s)
#print axioms on_scratch
end AspisR1.JGm_TX2_Valid2
end
