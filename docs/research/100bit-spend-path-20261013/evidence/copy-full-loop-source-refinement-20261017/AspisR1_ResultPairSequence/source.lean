import Aeneas.Std

/-! Generic tuple-bind sequencing. Proved on Result constructors before
instantiating generated array types; no scalar literal proof is normalized. -/
set_option autoImplicit false
namespace AspisR1.ResultPairSequence
open Aeneas.Std Result

theorem three_pair_bind {A B C D E F : Type}
    (w : Result A) (p : A → Result (B × C)) (q : A → Result (D × E))
    (k : B → C → D → E → Result F) :
    (do
      let value ← w
      let (b,c) ← p value
      let (d,e) ← q value
      k b c d e) = (do
      let (b,c,d,e) ← (do
        let value ← w
        let (b,c) ← p value
        let (d,e) ← q value
        ok (b,c,d,e))
      k b c d e) := by
  cases w with
  | fail err => rfl
  | div => rfl
  | ok value =>
    simp only [bind_tc_ok]
    cases hp : p value with
    | fail err => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨b,c⟩
      simp only [bind_tc_ok]
      cases hq : q value with
      | fail err => rfl
      | div => rfl
      | ok pair =>
        rcases pair with ⟨d,e⟩
        rfl

#print axioms three_pair_bind
end AspisR1.ResultPairSequence
