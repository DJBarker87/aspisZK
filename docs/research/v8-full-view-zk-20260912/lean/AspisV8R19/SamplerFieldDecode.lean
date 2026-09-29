import AspisV8R19.SamplerWrapperPolicies
import AspisV8R15.ExactTowerChord

/-! Interpret canonical sampler words in the retained exact deployed tower.
This is not a theorem extracting the Rust field implementation. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerFieldDecode
open AspisV8R15.ExactTowerBase AspisV8R15.ExactTowerChord

def decode4 (a b c d : Nat) : QM31Exact := ⟨⟨a,b⟩,⟨c,d⟩⟩
def decode : List Nat → QM31Exact
  | [a,b,c,d] => decode4 a b c d
  | _ => 0

theorem canonical_cast_zero (a : Nat) (ha : a < P) :
    (a : M31Exact) = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast_of_lt ha] using hv
  · intro h; simp [h]

theorem decode4_im_zero (a b c d : Nat) (hc : c < P) (hd : d < P) :
    (decode4 a b c d).im = 0 ↔ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    exact ⟨(canonical_cast_zero c hc).mp (congrArg (fun x : CM31Exact => x.re) h),
      (canonical_cast_zero d hd).mp (congrArg (fun x : CM31Exact => x.im) h)⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem decode4_zero (a b c d : Nat) (ha : a < P) (hb : b < P)
    (hc : c < P) (hd : d < P) :
    decode4 a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    exact ⟨(canonical_cast_zero a ha).mp (congrArg (fun x : QM31Exact => x.re.re) h),
      (canonical_cast_zero b hb).mp (congrArg (fun x : QM31Exact => x.re.im) h),
      (canonical_cast_zero c hc).mp (congrArg (fun x : QM31Exact => x.im.re) h),
      (canonical_cast_zero d hd).mp (congrArg (fun x : QM31Exact => x.im.im) h)⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩; rfl

theorem ood_policy_outside (xs ys : List Nat)
    (hc : ∀ a ∈ xs, a < P) (ha : SamplerWrapperPolicies.oodAccept xs = some ys) :
    (decode ys).im ≠ 0 := by
  obtain ⟨rfl,a,b,c,d,rfl,hne⟩ := SamplerWrapperPolicies.ood_policy xs ys ha
  exact fun h => hne ((decode4_im_zero a b c d (hc c (by simp)) (hc d (by simp))).mp h)

theorem decode_zero_iff (xs : List Nat) (hlen : xs.length = 4)
    (hc : ∀ a ∈ xs, a < P) : decode xs = 0 ↔ xs = [0,0,0,0] := by
  obtain ⟨a,b,c,d,hxs⟩ : ∃ a b c d, xs = [a,b,c,d] :=
    ⟨_,_,_,_,List.eq_getElem_of_length_eq_four xs hlen⟩
  subst xs
  rw [decode,decode4_zero a b c d (hc a (by simp)) (hc b (by simp))
    (hc c (by simp)) (hc d (by simp))]
  simp

theorem nonzero_field_result (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) (xs : List Nat)
    (h : (SamplerWrapperPolicies.nonzeroRun H s).2.1 = .ok xs) : decode xs ≠ 0 := by
  obtain ⟨hlen,hcan,hne⟩ := SamplerWrapperPolicies.nonzero_result H s xs h
  exact fun hz => hne ((decode_zero_iff xs hlen hcan).mp hz)

theorem ood_field_result (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) (xs : List Nat)
    (h : (SamplerWrapperPolicies.oodRun H s).2.1 = .ok xs) : (decode xs).im ≠ 0 := by
  obtain ⟨hcan,a,b,c,d,rfl,hne⟩ := SamplerWrapperPolicies.ood_result H s xs h
  exact fun hz => hne ((decode4_im_zero a b c d (hcan c (by simp))
    (hcan d (by simp))).mp hz)

#print axioms canonical_cast_zero
#print axioms decode4_im_zero
#print axioms decode4_zero
#print axioms ood_policy_outside
#print axioms decode_zero_iff
#print axioms nonzero_field_result
#print axioms ood_field_result
end AspisV8R19.SamplerFieldDecode
