import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EncoderPairTransport49
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)
def pairMap {A B : Type} (f : A → B) (p : A×A) : B×B := (f p.1,f p.2)
def run {A : Type} (mul add : A → A → Result A) (a b n p0 p1 : A) : Result (A×A) := do
  let an ← mul a n
  let p0 ← add p0 an
  let bn ← mul b n
  let p1 ← add p1 bn
  ok (p0,p1)

theorem complete {A B : Type} (f : A → B) (mul add : A → A → Result A)
    (mulB addB : B → B → Result B)
    (hm : ∀ a b, mulB (f a) (f b)=mapResult f (mul a b))
    (ha : ∀ a b, addB (f a) (f b)=mapResult f (add a b))
    (a b n p0 p1 : A) :
    run mulB addB (f a) (f b) (f n) (f p0) (f p1)=
      mapResult (pairMap f) (run mul add a b n p0 p1) := by
  unfold run
  rw [hm]
  cases h0 : mul a n with
  | fail e => rfl
  | div => rfl
  | ok an =>
    simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,ha]
    cases h1 : add p0 an with
    | fail e => rfl
    | div => rfl
    | ok v0 =>
      simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,hm]
      cases h2 : mul b n with
      | fail e => rfl
      | div => rfl
      | ok bn =>
        simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,ha]
        cases h3 : add p1 bn <;> rfl
#print axioms pairMap
#print axioms run
#print axioms complete
end R1Z.PV_RunJoin_EncoderPairTransport49
