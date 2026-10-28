import NDO_JGm_TX2_Level0_00
import NDO_JGm_TX2_Level0_01
import NDO_JGm_TX2_Level0_02
import NDO_JGm_TX2_Level0_03
import NDO_JGm_TX2_Level0_04
import NDO_JGm_TX2_Level0_05
import NDO_JGm_TX2_Level0_06
import NDO_JGm_TX2_Level0_07
import NDO_JGm_TX2_Level0_08
import NDO_JGm_TX2_Level0_09
import NDO_JGm_TX2_Level0_10
import NDO_JGm_TX2_Level0_11
import NDO_JGm_TX2_Level0_12
import NDO_JGm_TX2_Level0_13
import NDO_JGm_TX2_Level0_14
import NDO_JGm_TX2_Level0_15
import NDO_JGm_TX2_Level0_16
import NDO_JGm_TX2_Level0_17
import JGm_TX2_HeightTools
import NDO_JGm_TX2_Initial
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Levels0
open Aeneas Aeneas.Std Result MultiproofConeRef

def PhaseView (height : Nat) (s : reference.Scratch) : Prop := match height with
  | 0 => JGm_TX2_View.View s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0
  | 1 => JGm_TX2_View.View s JGm_TX2_Level0_01.indices00 JGm_TX2_Level0_01.values00 384
  | 2 => JGm_TX2_View.View s JGm_TX2_Level0_02.indices00 JGm_TX2_Level0_02.values00 768
  | 3 => JGm_TX2_View.View s JGm_TX2_Level0_03.indices00 JGm_TX2_Level0_03.values00 1152
  | 4 => JGm_TX2_View.View s JGm_TX2_Level0_04.indices00 JGm_TX2_Level0_04.values00 1536
  | 5 => JGm_TX2_View.View s JGm_TX2_Level0_05.indices00 JGm_TX2_Level0_05.values00 1920
  | 6 => JGm_TX2_View.View s JGm_TX2_Level0_06.indices00 JGm_TX2_Level0_06.values00 2304
  | 7 => JGm_TX2_View.View s JGm_TX2_Level0_07.indices00 JGm_TX2_Level0_07.values00 2688
  | 8 => JGm_TX2_View.View s JGm_TX2_Level0_08.indices00 JGm_TX2_Level0_08.values00 3072
  | 9 => JGm_TX2_View.View s JGm_TX2_Level0_09.indices00 JGm_TX2_Level0_09.values00 3456
  | 10 => JGm_TX2_View.View s JGm_TX2_Level0_10.indices00 JGm_TX2_Level0_10.values00 3840
  | 11 => JGm_TX2_View.View s JGm_TX2_Level0_11.indices00 JGm_TX2_Level0_11.values00 4224
  | 12 => JGm_TX2_View.View s JGm_TX2_Level0_12.indices00 JGm_TX2_Level0_12.values00 4544
  | 13 => JGm_TX2_View.View s JGm_TX2_Level0_13.indices00 JGm_TX2_Level0_13.values00 4896
  | 14 => JGm_TX2_View.View s JGm_TX2_Level0_14.indices00 JGm_TX2_Level0_14.values00 5120
  | 15 => JGm_TX2_View.View s JGm_TX2_Level0_15.indices00 JGm_TX2_Level0_15.values00 5152
  | 16 => JGm_TX2_View.View s JGm_TX2_Level0_16.indices00 JGm_TX2_Level0_16.values00 5184
  | 17 => JGm_TX2_View.View s JGm_TX2_Level0_17.indices00 JGm_TX2_Level0_17.values00 5216
  | 18 => JGm_TX2_View.View s JGm_TX2_Level0_17.indicesOut JGm_TX2_Level0_17.valuesOut 5216
  | _ => False

theorem step {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (h : Nat) (bound : h<18) (s : reference.Scratch) (view : PhaseView h s) :
    ∃ out, reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGm_TX2_Supplied.nodes0 0#usize 0#usize=ok (.Done out) ∧ PhaseView (h+1) out := by
  interval_cases h
  · exact ⟨_,JGm_TX2_Level0_00.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_01.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_02.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_03.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_04.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_05.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_06.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_07.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_08.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_09.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_10.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_11.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_12.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_13.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_14.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_15.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_16.source D hash s view⟩
  · exact ⟨_,JGm_TX2_Level0_17.source D hash s view⟩
#print axioms step

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash s
      JGm_TX2_Supplied.nodes0 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JGm_TX2_Level0_17.indicesOut JGm_TX2_Level0_17.valuesOut 5216 := by
  obtain ⟨out,run,last⟩ := JGm_TX2_HeightTools.compose (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGc_TX2_RealLeaves.dictionary D)) hash state JGm_TX2_Supplied.nodes0 0#usize 0#usize) 18 PhaseView (step D hash) s view
  refine ⟨out,?_,last⟩
  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  exact run
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
