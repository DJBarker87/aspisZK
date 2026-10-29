import R1Z.PV_RunJoin_EncoderPairTransport49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderFinalTransport49
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_EncoderPairTransport49 (pairMap)
theorem complete {A B : Type} (f : A → B) (mul add : A → A → Result A)
    (mulB addB : B → B → Result B)
    (hm : ∀ a b, mulB (f a) (f b)=mapResult f (mul a b))
    (ha : ∀ a b, addB (f a) (f b)=mapResult f (add a b))
    (r : Result (A×A)) (y : A) :
    (do let p ← mapResult (pairMap f) r
        let product ← mulB (f y) p.2
        addB p.1 product)=
      mapResult f (do
        let p ← r
        let product ← mul y p.2
        add p.1 product) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok p =>
    rcases p with ⟨p0,p1⟩
    simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,pairMap,hm]
    cases h : mul y p1 with
    | fail e => rfl
    | div => rfl
    | ok x =>
      simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok]
      exact ha p0 x
#print axioms complete
end R1Z.PV_RunJoin_EncoderFinalTransport49
