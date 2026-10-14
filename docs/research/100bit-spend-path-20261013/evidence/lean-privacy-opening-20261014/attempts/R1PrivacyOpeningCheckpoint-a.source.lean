import R1DualPadWord
import R1DualPadLift
import R1OpeningSamplerBound

/-! Focused axiom checkpoint for the generic dual-pad word identities, their
quadratic lift, and the existing opening sampler bound. This imports and audits
those declarations; it adds no privacy theorem or source correspondence. -/

#print axioms AspisR1.DualPadWord.repair_mem
#print axioms AspisR1.DualPadWord.repair_eq
#print axioms AspisR1.DualPadWord.repair_raw_zero
#print axioms AspisR1.DualPadWord.full_word_eq
#print axioms AspisR1.DualPadWord.correction

#print axioms AspisR1.DualPadLift.coefficients_cancel
#print axioms AspisR1.DualPadLift.correction
#print axioms AspisR1.DualPadLift.observations_eq

#print axioms AspisR1.OpeningSamplerBound.gamma_mass_le
#print axioms AspisR1.OpeningSamplerBound.gammaSample_ne_zero
#print axioms AspisR1.OpeningSamplerBound.kappa_mass_le
#print axioms AspisR1.OpeningSamplerBound.first_mass_le
#print axioms AspisR1.OpeningSamplerBound.second_mass_le
#print axioms AspisR1.OpeningSamplerBound.openingCap_lt_two_neg_199
