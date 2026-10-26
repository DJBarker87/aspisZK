import R1Z.PV_RW_Outcome
set_option autoImplicit false
namespace R1Z.PV_RW_OutcomeIso
open PV_RW_Outcome

theorem left_inverse {E A B : Type} (encode : A → B) (decode : B → A)
    (roundtrip : ∀ a, decode (encode a)=a) (result : Outcome E A) :
    map id decode (map id encode result)=result := by
  cases result with
  | ok a => exact congrArg Outcome.ok (roundtrip a)
  | fail error => rfl
  | div => rfl

theorem injective {E A B : Type} (encode : A → B) (decode : B → A)
    (roundtrip : ∀ a, decode (encode a)=a) (left right : Outcome E A)
    (same : map id encode left=map id encode right) : left=right := by
  calc
    left=map id decode (map id encode left) := (left_inverse encode decode roundtrip left).symm
    _=map id decode (map id encode right) := congrArg (map id decode) same
    _=right := left_inverse encode decode roundtrip right

theorem equal_iff {E A B : Type} (encode : A → B) (decode : B → A)
    (roundtrip : ∀ a, decode (encode a)=a) (left right : Outcome E A) :
    map id encode left=map id encode right ↔ left=right := by
  constructor
  · exact injective encode decode roundtrip left right
  · exact congrArg (map id encode)
#print axioms left_inverse
#print axioms injective
#print axioms equal_iff
end R1Z.PV_RW_OutcomeIso
