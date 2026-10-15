import R1SelectedOpeningStages
import R1SelectedOpeningRead

/-! Earlier staged payload views agree with a successful complete opening
payload read. Together with stage append stability this identifies the same
payloads across cuts. Challenge and committed-word correspondence are separate.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedOpeningStageConsistency

open AspisR1.SelectedOpeningStages

def gamma (p : SelectedOpeningData.Payloads) : Gamma :=
  ⟨p.row25, p.row26, p.row27⟩

def kappa (p : SelectedOpeningData.Payloads) : Kappa := ⟨gamma p, p.row28⟩
def first (p : SelectedOpeningData.Payloads) : First := ⟨kappa p, p.row29⟩
def second (p : SelectedOpeningData.Payloads) : Second := ⟨first p, p.row30⟩

theorem stages_of_full (rs : List InitialWalk.RawRec)
    (p : SelectedOpeningData.Payloads) (h : SelectedOpeningRead.read rs = some p) :
    readGamma rs = some (gamma p) ∧ readKappa rs = some (kappa p) ∧
    readFirst rs = some (first p) ∧ readSecond rs = some (second p) := by
  obtain ⟨h25, h26, h27, h28, h29, h30, _h31⟩ :=
    (SelectedOpeningRead.read_eq_some_iff rs p).mp h
  have hg : readGamma rs = some (gamma p) := by
    simp [readGamma, h25, h26, h27, gamma]
  have hk : readKappa rs = some (kappa p) := by
    simp [readKappa, hg, h28, kappa]
  have hf : readFirst rs = some (first p) := by
    simp [readFirst, hk, h29, first]
  have hs : readSecond rs = some (second p) := by
    simp [readSecond, hf, h30, second]
  exact ⟨hg, hk, hf, hs⟩

theorem gamma_at_prefix (rs tail : List InitialWalk.RawRec)
    (p : SelectedOpeningData.Payloads)
    (h : SelectedOpeningRead.read (rs ++ tail) = some p)
    (hlen : 27 < rs.length) : readGamma rs = some (gamma p) := by
  have hs := (stages_of_full (rs ++ tail) p h).1
  rw [readGamma_append_stable rs tail hlen] at hs
  exact hs

theorem kappa_at_prefix (rs tail : List InitialWalk.RawRec)
    (p : SelectedOpeningData.Payloads)
    (h : SelectedOpeningRead.read (rs ++ tail) = some p)
    (hlen : 28 < rs.length) : readKappa rs = some (kappa p) := by
  have hs := (stages_of_full (rs ++ tail) p h).2.1
  rw [readKappa_append_stable rs tail hlen] at hs
  exact hs

theorem first_at_prefix (rs tail : List InitialWalk.RawRec)
    (p : SelectedOpeningData.Payloads)
    (h : SelectedOpeningRead.read (rs ++ tail) = some p)
    (hlen : 29 < rs.length) : readFirst rs = some (first p) := by
  have hs := (stages_of_full (rs ++ tail) p h).2.2.1
  rw [readFirst_append_stable rs tail hlen] at hs
  exact hs

theorem second_at_prefix (rs tail : List InitialWalk.RawRec)
    (p : SelectedOpeningData.Payloads)
    (h : SelectedOpeningRead.read (rs ++ tail) = some p)
    (hlen : 30 < rs.length) : readSecond rs = some (second p) := by
  have hs := (stages_of_full (rs ++ tail) p h).2.2.2
  rw [readSecond_append_stable rs tail hlen] at hs
  exact hs

#print axioms stages_of_full
#print axioms gamma_at_prefix
#print axioms kappa_at_prefix
#print axioms first_at_prefix
#print axioms second_at_prefix

end AspisR1.SelectedOpeningStageConsistency
end
