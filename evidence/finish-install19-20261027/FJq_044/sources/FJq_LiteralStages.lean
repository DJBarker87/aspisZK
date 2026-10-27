import R1LiteralOpeningStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_LiteralStages
/-- Later strict reads retain the exact first three decoded payloads. -/
theorem reached (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (out : LiteralOpeningStages.Second) (run : LiteralOpeningStages.readSecond rs=some out) :
    LiteralOpeningStages.readGamma rs=some out.toFirst.toKappa.toGamma := by
  unfold LiteralOpeningStages.readSecond at run
  obtain ⟨first,hfirst,run⟩:=Option.bind_eq_some_iff.mp run
  obtain ⟨row30,h30,run⟩:=Option.bind_eq_some_iff.mp run
  have same:=Option.some.inj run
  subst out
  unfold LiteralOpeningStages.readFirst at hfirst
  obtain ⟨kappa,hkappa,hfirst⟩:=Option.bind_eq_some_iff.mp hfirst
  obtain ⟨row29,h29,hfirst⟩:=Option.bind_eq_some_iff.mp hfirst
  have same:=Option.some.inj hfirst
  subst first
  unfold LiteralOpeningStages.readKappa at hkappa
  obtain ⟨gamma,hgamma,hkappa⟩:=Option.bind_eq_some_iff.mp hkappa
  obtain ⟨row28,h28,hkappa⟩:=Option.bind_eq_some_iff.mp hkappa
  have same:=Option.some.inj hkappa
  subst kappa
  exact hgamma
#print axioms reached
end AspisR1.FJq_LiteralStages
end
