import JGm_TX2_Level0_00
import JGm_TX2_Level0_01
import JGm_TX2_Level0_02
import JGm_TX2_Level0_03
import JGm_TX2_Level0_04
import JGm_TX2_Level0_05
import JGm_TX2_Level0_06
import JGm_TX2_Level0_07
import JGm_TX2_Level0_08
import JGm_TX2_Level0_09
import JGm_TX2_Level0_10
import JGm_TX2_Level0_11
import JGm_TX2_Level0_12
import JGm_TX2_Level0_13
import JGm_TX2_Level0_14
import JGm_TX2_Level0_15
import JGm_TX2_Level0_16
import JGm_TX2_Level0_17
import MultiproofConeLevelIteration
import JGm_TX2_Initial
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Levels0
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGm_TX2_Supplied.nodes0 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGm_TX2_Level0_17.indicesOut JGm_TX2_Level0_17.valuesOut 5216 := by
  obtain ⟨s01,r00,v01⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_00.indicesOut JGm_TX2_Level0_00.valuesOut 384 :=
    ⟨_,JGm_TX2_Level0_00.source D hash s view⟩
  obtain ⟨s02,r01,v02⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s01
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_01.indicesOut JGm_TX2_Level0_01.valuesOut 768 :=
    ⟨_,JGm_TX2_Level0_01.source D hash s01 v01⟩
  obtain ⟨s03,r02,v03⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s02
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_02.indicesOut JGm_TX2_Level0_02.valuesOut 1152 :=
    ⟨_,JGm_TX2_Level0_02.source D hash s02 v02⟩
  obtain ⟨s04,r03,v04⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s03
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_03.indicesOut JGm_TX2_Level0_03.valuesOut 1536 :=
    ⟨_,JGm_TX2_Level0_03.source D hash s03 v03⟩
  obtain ⟨s05,r04,v05⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s04
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_04.indicesOut JGm_TX2_Level0_04.valuesOut 1920 :=
    ⟨_,JGm_TX2_Level0_04.source D hash s04 v04⟩
  obtain ⟨s06,r05,v06⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s05
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_05.indicesOut JGm_TX2_Level0_05.valuesOut 2304 :=
    ⟨_,JGm_TX2_Level0_05.source D hash s05 v05⟩
  obtain ⟨s07,r06,v07⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s06
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_06.indicesOut JGm_TX2_Level0_06.valuesOut 2688 :=
    ⟨_,JGm_TX2_Level0_06.source D hash s06 v06⟩
  obtain ⟨s08,r07,v08⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s07
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_07.indicesOut JGm_TX2_Level0_07.valuesOut 3072 :=
    ⟨_,JGm_TX2_Level0_07.source D hash s07 v07⟩
  obtain ⟨s09,r08,v09⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s08
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_08.indicesOut JGm_TX2_Level0_08.valuesOut 3456 :=
    ⟨_,JGm_TX2_Level0_08.source D hash s08 v08⟩
  obtain ⟨s10,r09,v10⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s09
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_09.indicesOut JGm_TX2_Level0_09.valuesOut 3840 :=
    ⟨_,JGm_TX2_Level0_09.source D hash s09 v09⟩
  obtain ⟨s11,r10,v11⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s10
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_10.indicesOut JGm_TX2_Level0_10.valuesOut 4224 :=
    ⟨_,JGm_TX2_Level0_10.source D hash s10 v10⟩
  obtain ⟨s12,r11,v12⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s11
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_11.indicesOut JGm_TX2_Level0_11.valuesOut 4544 :=
    ⟨_,JGm_TX2_Level0_11.source D hash s11 v11⟩
  obtain ⟨s13,r12,v13⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s12
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_12.indicesOut JGm_TX2_Level0_12.valuesOut 4896 :=
    ⟨_,JGm_TX2_Level0_12.source D hash s12 v12⟩
  obtain ⟨s14,r13,v14⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s13
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_13.indicesOut JGm_TX2_Level0_13.valuesOut 5120 :=
    ⟨_,JGm_TX2_Level0_13.source D hash s13 v13⟩
  obtain ⟨s15,r14,v15⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s14
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_14.indicesOut JGm_TX2_Level0_14.valuesOut 5152 :=
    ⟨_,JGm_TX2_Level0_14.source D hash s14 v14⟩
  obtain ⟨s16,r15,v16⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s15
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_15.indicesOut JGm_TX2_Level0_15.valuesOut 5184 :=
    ⟨_,JGm_TX2_Level0_15.source D hash s15 v15⟩
  obtain ⟨s17,r16,v17⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s16
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_16.indicesOut JGm_TX2_Level0_16.valuesOut 5216 :=
    ⟨_,JGm_TX2_Level0_16.source D hash s16 v16⟩
  obtain ⟨s18,r17,v18⟩ : ∃ out,
      reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s17
        JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧
      JGm_TX2_View.View out JGm_TX2_Level0_17.indicesOut JGm_TX2_Level0_17.valuesOut 5216 :=
    ⟨_,JGm_TX2_Level0_17.source D hash s17 v17⟩
  refine ⟨s18,?_,v18⟩
  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 18 s=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r00]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 17 s01=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r01]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 16 s02=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r02]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 15 s03=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r03]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 14 s04=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r04]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 13 s05=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r05]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 12 s06=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r06]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 11 s07=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r07]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 10 s08=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r08]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 9 s09=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r09]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 8 s10=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r10]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 7 s11=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r11]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 6 s12=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r12]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 5 s13=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r13]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 4 s14=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r14]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 3 s15=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r15]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 2 s16=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r16]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 1 s17=ok (.Done s18)
  rw [MultiproofConeLevelIteration.iterate,r17]
  change MultiproofConeLevelIteration.iterate (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 0 s18=ok (.Done s18)
  rfl
#print axioms source
 theorem on_scratch {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash
      (JGk_TX2_Scratch0.s12 s) JGm_TX2_Supplied.nodes0 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGm_TX2_Level0_17.indicesOut JGm_TX2_Level0_17.valuesOut 5216 :=
  source D hash _ (JGm_TX2_Initial0.source s)
#print axioms on_scratch
end AspisR1.JGm_TX2_Levels0
end
