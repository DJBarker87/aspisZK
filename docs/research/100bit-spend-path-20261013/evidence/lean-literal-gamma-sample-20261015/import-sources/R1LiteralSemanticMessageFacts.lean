import R1LiteralSemanticPrefix

/-! Constructor-valid literal messages erase to messages accepted by the
unified sampler's schedule. Invalid literal messages are rejected by the
literal semantic parser. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticMessageFacts

theorem valid_erased (i : Nat) (m : LiteralTranscript.Message)
    (h : LiteralTranscript.valid i m) :
    UnifiedSampler.messageValid i (LiteralTranscript.erase m) := by
  cases i with
  | zero =>
      cases m <;>
        simp [LiteralTranscript.valid, LiteralTranscript.erase,
          UnifiedSampler.messageValid] at h ⊢
  | succ i =>
      cases m <;>
        simp [LiteralTranscript.valid, LiteralTranscript.erase,
          UnifiedSampler.messageValid] at h ⊢

theorem parseMessage_none_of_not_valid
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (row : Fin 25) (m : LiteralTranscript.Message)
    (h : ¬ LiteralTranscript.valid row.val m) :
    LiteralSemanticPrefix.parseMessage eK row m = none := by
  simp [LiteralSemanticPrefix.parseMessage, h]

#print axioms valid_erased
#print axioms parseMessage_none_of_not_valid

end AspisR1.LiteralSemanticMessageFacts
end
