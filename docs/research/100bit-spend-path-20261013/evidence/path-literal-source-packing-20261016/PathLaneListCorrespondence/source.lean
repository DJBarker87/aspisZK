import PathLaneLiteralExecution
import PathLaneListFacts
import SelectorValueLanePreprocessRangeValues

/-! The returned source array is the exact retained 17-cell path list,
using the same opening representation already proved for the value family. -/
set_option autoImplicit false
namespace AspisR1.PathLaneListCorrespondence
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PathLaneSourceStep
open AspisR1.PathLaneSourceLoop
open AspisR1.PathLaneSourcePrefix
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskQM31Exact

abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings

def exactVector (values : Array QM 17#usize) : Fin 17 → ExactQM :=
  fun i => decode (cell values i)

private theorem read_z (openings : Openings) (i : Fin 16) :
    read16 openings.z i.val = (exactOpenings openings).z i := by
  simp only [read16, dif_pos i.isLt, exactOpenings,
    AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings, cell]

private theorem read_succ (openings : Openings) (i : Fin 16) :
    read16 openings.succ_z i.val = (exactOpenings openings).succ i := by
  simp only [read16, dif_pos i.isLt, exactOpenings,
    AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings, cell]

private theorem left_exact (selector : QM) (openings : Openings) (i : Fin 8) :
    left selector (cell openings.z bitIndex) openings.z openings.succ_z i.val =
      decode selector * (1 - (exactOpenings openings).z 0) *
        ((exactOpenings openings).succ (i.castAdd 8) -
          (exactOpenings openings).z (i.addNat 1 |>.castLE (by omega))) := by
  have hb : decode (cell openings.z bitIndex) = (exactOpenings openings).z 0 := rfl
  have hs : read16 openings.succ_z i.val = (exactOpenings openings).succ (i.castAdd 8) :=
    read_succ openings (i.castAdd 8)
  have hz : read16 openings.z (1 + i.val) =
      (exactOpenings openings).z (i.addNat 1 |>.castLE (by omega)) := by
    have hindex : ((i.addNat 1 |>.castLE (by omega)) : Fin 16).val = 1 + i.val := by
      change i.val + 1 = 1 + i.val
      omega
    simpa only [hindex] using read_z openings (i.addNat 1 |>.castLE (by omega))
  simp only [left, hb, hs, hz]

private theorem right_exact (selector : QM) (openings : Openings) (i : Fin 8) :
    right selector (cell openings.z bitIndex) openings.z openings.succ_z i.val =
      decode selector * (exactOpenings openings).z 0 *
        ((exactOpenings openings).succ (i.natAdd 8) -
          (exactOpenings openings).z (i.addNat 1 |>.castLE (by omega))) := by
  have hb : decode (cell openings.z bitIndex) = (exactOpenings openings).z 0 := rfl
  have hs : read16 openings.succ_z (8 + i.val) = (exactOpenings openings).succ (i.natAdd 8) :=
    read_succ openings (i.natAdd 8)
  have hz : read16 openings.z (1 + i.val) =
      (exactOpenings openings).z (i.addNat 1 |>.castLE (by omega)) := by
    have hindex : ((i.addNat 1 |>.castLE (by omega)) : Fin 16).val = 1 + i.val := by
      change i.val + 1 = 1 + i.val
      omega
    simpa only [hindex] using read_z openings (i.addNat 1 |>.castLE (by omega))
  simp only [right, hb, hs, hz]

theorem literal_list (selector : QM) (openings : Openings)
    (hs : Canonical selector) (hz : CanonicalArray openings.z)
    (hsucc : CanonicalArray openings.succ_z) :
    ∃ values : Array QM 17#usize,
      AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal
        selector openings = .ok values ∧ CanonicalArray values ∧
      List.ofFn (exactVector values) = R0P.pathLanes (decode selector) (exactOpenings openings) := by
  obtain ⟨values, hrun, hcanonical, hzero, hleft, hright⟩ :=
    AspisR1.PathLaneLiteralExecution.literal_execution selector openings hs hz hsucc
  refine ⟨values, hrun, hcanonical, ?_⟩
  apply List.ext_getElem
  · simp [R0P.pathLanes]
  · intro n hL hR
    have hn : n < 17 := by simpa [R0P.pathLanes] using hR
    rw [List.getElem_ofFn]
    change decode (cell values (⟨n, hn⟩ : Fin 17)) = _
    by_cases hn0 : n = 0
    · subst n
      have hb : decode (cell openings.z bitIndex) = (exactOpenings openings).z 0 := rfl
      change decode (cell values (⟨0, hn⟩ : Fin 17)) =
        decode selector * (decode (cell openings.z bitIndex) *
          (decode (cell openings.z bitIndex) - 1)) at hzero
      have hactual := hzero.trans
        (congrArg (fun x : ExactQM => decode selector * (x * (x - 1))) hb)
      exact hactual.trans
        (AspisR1.PathLaneListFacts.bit_cell (decode selector) (exactOpenings openings)).symm
    · by_cases hn9 : n < 9
      · let i : Fin 8 := ⟨n - 1, by omega⟩
        have hi : 1 + i.val = n := by dsimp [i]; omega
        have hactual := (hleft i).trans (left_exact selector openings i)
        have hlist := AspisR1.PathLaneListFacts.left_cell (decode selector) (exactOpenings openings) i
        have hactualn := hactual
        simp only [hi] at hactualn hlist
        exact hactualn.trans hlist.symm
      · let i : Fin 8 := ⟨n - 9, by omega⟩
        have hi : 9 + i.val = n := by dsimp [i]; omega
        have hactual := (hright i).trans (right_exact selector openings i)
        have hlist := AspisR1.PathLaneListFacts.right_cell (decode selector) (exactOpenings openings) i
        have hactualn := hactual
        simp only [hi] at hactualn hlist
        exact hactualn.trans hlist.symm

#print axioms literal_list
end
end AspisR1.PathLaneListCorrespondence
