import TerminalV4CurrentArithmeticContractV2
import TerminalV4QM31ExactV5
import TerminalV4ConstantsV1

set_option autoImplicit false

namespace AspisR1.TerminalV4CurrentArithmeticInstantiation

abbrev CurrentQM := AspisR1.TerminalV4QM31Exact.CurrentQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

/-- Exact operation laws for the current generated terminal suffix. -/
def laws : AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.Laws ExactQM where
  decode := AspisR1.TerminalV4QM31Exact.decode
  one := 1
  canonical := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM
  add_exact := AspisR1.TerminalV4QM31Exact.current_qm_add_exact
  sub_exact := AspisR1.TerminalV4QM31Exact.current_qm_sub_exact
  mul_exact := AspisR1.TerminalV4QM31Exact.current_qm_mul_exact
  one_canonical := AspisR1.TerminalV4Constants.one_canonical
  one_decode := AspisR1.TerminalV4Constants.one_decode

theorem run_exact (q composition h1Z copyActive mu : CurrentQM)
    (hq : laws.canonical q) (hc : laws.canonical composition)
    (hh : laws.canonical h1Z) (ha : laws.canonical copyActive)
    (hm : laws.canonical mu) :
    ∃ out, AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run
        q composition h1Z copyActive mu = .ok out ∧
      laws.canonical out ∧
      laws.decode out =
        (laws.decode q * laws.decode composition + laws.decode mu * laws.decode h1Z) +
        (laws.decode mu * laws.decode mu) *
          ((laws.one - laws.decode copyActive) * laws.decode h1Z) := by
  exact AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run_exact
    laws q composition h1Z copyActive mu hq hc hh ha hm

#print axioms run_exact

end AspisR1.TerminalV4CurrentArithmeticInstantiation
