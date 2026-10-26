import R1Z.PV_RunJoin_ZeroizingPrefix
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroizingBefore
open Aeneas Aeneas.Std Result ProverRwFull

theorem before_returns (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    letI : ExternalFuns := PV_RunJoin_ZeroizingPrefix.selected base ops
    ∃ input back, ProverRwEffectSource.before = .ok (input,back) := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  letI : ExternalFuns := PV_RunJoin_ZeroizingPrefix.selected base ops
  unfold ProverRwEffectSource.before
  simp only [zeroize.Zeroizing.new,zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut,
    PV_RunJoin_ZeroizingPrefix.selected,PV_RunJoin_ZeroizingPrefix.newValue,
    PV_RunJoin_ZeroizingPrefix.asMut,bind_tc_ok]
  exact ⟨_,_,rfl⟩

#print axioms before_returns
end R1Z.PV_RunJoin_ZeroizingBefore
