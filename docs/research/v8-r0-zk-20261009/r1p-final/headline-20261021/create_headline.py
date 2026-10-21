from pathlib import Path
root = Path(__file__).resolve().parents[2]
lean = root / 'lean/R1Z'
q = (lean / 'PrivacyR1FinalProtocolQuotient.lean').read_text()
s = (lean / 'PrivacyR1FinalReleaseSource.lean').read_text()
pre = q[q.index('set_option'):q.index('theorem privacy_R1_protocol_quotient_of_lazy_budget')]
pre = pre.replace('namespace R1Z.PrivacyR1FinalProtocolQuotient', 'namespace R1Z.PrivacyR1Headline')
pre = pre.replace(' (publicWidth : ℕ)', '')
adapters = '''/-- The common builder contract asks only for facts used at matching witnesses. -/
def BuilderPremises : Prop :=
  ∀ w : h.Instance, h.public w = x.1 →
    PublicBase F x.1 ∧ R0Z.HonestValidity.BuilderSoundOn h B x

theorem builder_premises_of_protocol
    (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) : BuilderPremises h B x :=
  fun _ _ => ⟨hpub, hs⟩

local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

/-- D101--D103's source join supplies the common contract without a tape premise. -/
theorem builder_premises_of_source
    (join : BuilderRuntimeJoin.RustRuntimeJoin h) : BuilderPremises h B x := by
  intro w hw
  constructor
  · rw [← hw, join.public_eq w]
    exact BuilderCanonical.publicBase_map F _
  · exact BuilderRuntimeJoin.builder_refinement_D46_D51
      BuilderProtocolInstance.field_large F B x join

/-- D96/D99's canonical builder is the source-free specialization. -/
theorem builder_premises_canonical :
    BuilderPremises (BuilderSource.prover («K» := K)) B x := by
  intro w hw
  constructor
  · rw [← hw]
    exact BuilderCanonical.publicBase_map F w.val.1
  · exact BuilderProtocolInstance.builder_sound B x

'''
stmt = q[q.index('theorem privacy_R1_protocol_quotient\n'):q.index(' := by',q.index('theorem privacy_R1_protocol_quotient\n'))]
stmt = stmt.replace('privacy_R1_protocol_quotient', 'privacy_headline', 1)
stmt = stmt.replace('    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)\n    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)', '    (hB : R0Z.K4.PackField B)\n    (builder_premises : BuilderPremises h B x)')
proof = s[s.index(' := by\n  constructor'):s.index('\n#print axioms')]
start = proof.index('    have hpub')
end = proof.index('      cF R_commit_equal_fibres')
proof = proof[:start] + '''    obtain ⟨hpub, hs⟩ := builder_premises w hw
    exact (PrivacyR1FinalProtocolQuotient.privacy_R1_protocol_quotient
      base h B outputs x seed hB hpub hs
''' + proof[end:]
proof = proof.replace('R_commit_equal_fibres', 'R_commit_quotient_fibres')
text = '''import R1Z.PrivacyR1FinalProtocolQuotient
import R1Z.PrivacyR1FinalReleaseSource3

/-! Common privacy headline: D100's quotient law and the builder contracts
proved by D96/D99 and D101--D103. No Rust correspondence is manufactured. -/
''' + pre + adapters + stmt + proof + '''
#print axioms builder_premises_of_protocol
#print axioms builder_premises_of_source
#print axioms builder_premises_canonical
#print axioms privacy_headline
end R1Z.PrivacyR1Headline
'''
(lean / 'PrivacyR1Headline.lean').write_text(text)
