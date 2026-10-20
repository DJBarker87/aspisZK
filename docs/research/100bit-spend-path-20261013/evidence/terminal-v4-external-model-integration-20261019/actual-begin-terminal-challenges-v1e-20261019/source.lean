import ActualBeginSelectedCanonical
import SemanticCallSelectedCanonical
import AspisR1SelectedMaskProbe.Types

/-! The current Rust caller passes the successful `r1_wire::begin` result
through a six-field record copy before `terminal_qm31`.  `r1_wire::Challenges`
is a re-export of the core challenge type in Rust; this adapter makes the
same field copy explicit across the public-preparation and selected-terminal
Lean carriers. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.TerminalV4ActualBeginTerminalChallenges
open AspisR1PublicPreparation.ActualBeginSelectedCanonical

abbrev InputChallenges := AspisR1PublicPreparation.r1_wire.Challenges
abbrev OutputChallenges := AspisR1SelectedMaskProbe.state_only_prefix.r0.Challenges
abbrev ToSelected := AspisR1PublicPreparation.SemanticCallSelectedCanonical.toSelected
abbrev SelectedCanonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def selectedChallengeArray (a : Array AspisR1PublicPreparation.aspis_core.field.QM31 10#usize) :
    Array AspisR1SelectedMaskProbe.field.QM31 10#usize :=
  ⟨a.val.map ToSelected, by simp [a.property]⟩

/-- The source's `original_challenges` record literal, transported to the
selected carrier consumed by the current terminal model. -/
def terminalChallenges (c : InputChallenges) : OutputChallenges :=
  { lambda := ToSelected c.lambda
    chi := ToSelected c.chi
    theta := ToSelected c.theta
    zc := selectedChallengeArray c.zc
    mu := ToSelected c.mu
    eta := ToSelected c.eta }

theorem terminalChallenges_mu (c : InputChallenges) :
    (terminalChallenges c).mu = ToSelected c.mu := rfl

theorem terminalChallenges_lambda (c : InputChallenges) :
    (terminalChallenges c).lambda = ToSelected c.lambda := rfl

theorem terminalChallenges_eta (c : InputChallenges) :
    (terminalChallenges c).eta = ToSelected c.eta := rfl

/-- The μ coordinate copied into the actual terminal input is canonical when
the exact `r1_wire::begin` result is successful.  No second challenge run is
introduced: `hbegin` supplies the very record consumed by the source copy. -/
theorem begin_terminal_mu_canonical {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : InputChallenges)
    (hbegin : AspisR1PublicPreparation.r1_wire.begin D pre before =
      ok (.Ok challenges, after)) :
    SelectedCanonical (terminalChallenges challenges).mu := by
  have hcanon := begin_challenges_selected_canonical
    D pre before after challenges hbegin
  rw [terminalChallenges_mu]
  exact hcanon.2.2.2.1

#print axioms terminalChallenges_mu
#print axioms begin_terminal_mu_canonical
end AspisR1.TerminalV4ActualBeginTerminalChallenges
