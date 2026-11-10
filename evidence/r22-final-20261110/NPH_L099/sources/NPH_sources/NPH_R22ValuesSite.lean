import NPH_R22Values

/-! NPH_ (R22 item 3, the prepare op11 site at the installed configurations). At every installed
configuration the op11 slot of currentInstalled is AspisS1ValuesOwnedInstallation.expandValues
(`installed_op11`, also after the op8 replacement of NPH_R22JoinCW6), and the Y1 window
proof[OFF_Y1, OFF_INACTIVE) read by candidate.prepare before that call has constant bounds whose
width is at most 1856 (`installed_window`). With NPH_R22Values.prepare_site this makes the checked
2 * len of values_owned_reference ok at that call (`installed_y1_site`). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22ValuesSite
open Aeneas Aeneas.Std Result

theorem installed_op11 {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C) :
    (AspisR1.DrvC_Installation.currentInstalled cfg).op11 = AspisS1ValuesOwnedInstallation.expandValues ∧
    ({ AspisR1.DrvC_Installation.currentInstalled cfg with op8 := AspisR1.NPH_R22JoinCW6.guardedOp8 }).op11 =
      AspisS1ValuesOwnedInstallation.expandValues :=
  ⟨rfl, rfl⟩

theorem installed_window {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C) :
    ∃ a b : Usize,
      AspisR1CurrentCaller.compact.OFF_Y1 (AspisR1.DrvC_Installation.currentInstalled cfg) = ok a ∧
      AspisR1CurrentCaller.compact.OFF_INACTIVE (AspisR1.DrvC_Installation.currentInstalled cfg) = ok b ∧
      b.val - a.val ≤ 1856 := by
  refine ⟨_, _, ?_, ?_, ?_⟩
  · unfold AspisR1CurrentCaller.compact.OFF_Y1 AspisR1CurrentCaller.compact.OFF_SEMANTIC; rfl
  · unfold AspisR1CurrentCaller.compact.OFF_INACTIVE AspisR1CurrentCaller.compact.OFF_Y1
      AspisR1CurrentCaller.compact.OFF_SEMANTIC; rfl
  · decide

theorem installed_y1_site {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C)
    (proof s2 : Slice U8) (a b : Usize)
    (ha : AspisR1CurrentCaller.compact.OFF_Y1 (AspisR1.DrvC_Installation.currentInstalled cfg) = ok a)
    (hb : AspisR1CurrentCaller.compact.OFF_INACTIVE (AspisR1.DrvC_Installation.currentInstalled cfg) = ok b)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
      { start := a, «end» := b } = ok s2) :
    s2.val.length ≤ 1856 ∧
      ∃ z, (2#usize * alloc.vec.Vec.len (AspisS1ValuesOwnedInstallation.toVec s2) : Result Usize) = ok z ∧
        z.val = 2 * s2.val.length := by
  obtain ⟨a', b', ha', hb', w⟩ := installed_window cfg
  have ea : a' = a := Result.ok.inj (ha'.symm.trans ha)
  have eb : b' = b := Result.ok.inj (hb'.symm.trans hb)
  subst ea; subst eb
  exact NPH_R22Values.prepare_site proof s2 a' b' w read

#print axioms installed_op11
#print axioms installed_window
#print axioms installed_y1_site
end AspisR1.NPH_R22ValuesSite
