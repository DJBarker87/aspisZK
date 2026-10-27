import XSa_ClaimDot
import XRy_ClaimPartFactor
import XSa_OptionFold
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PartFold

def step {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat)
 (st : Dot × Dot) (l : Nat) : Result (Option (Dot × Dot)) := do
 let q ← XRy_ClaimSelect.read (es sem) s point l
 if XSa_CheckedQ.valid q then do
   let v ← Array.index_usize g (XRn_Join_usize l)
   let a ← _root_.fast_pairing.canonical.Dot.push st.1 (XRn_Join_toQ (eq v.c0)) (XRn_Join_toQ q)
   let b ← _root_.fast_pairing.canonical.Dot.push st.2 (XRn_Join_toQ (eq v.c1)) (XRn_Join_toQ q)
   ok (some (a,b))
 else ok none

def oldStep {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat)
 (st : Option (Dot × Dot)) (l : Nat) : Result (Option (Dot × Dot)) := do
 match st with
 | none => ok none
 | some (a,b) =>
   let q ← XRy_ClaimSelect.read (es sem) s point l
   if !(XSa_CheckedQ.valid q) then ok none else do
     let v ← Array.index_usize g (XRn_Join_usize l)
     let a ← _root_.fast_pairing.canonical.Dot.push a (XRn_Join_toQ (eq v.c0)) (XRn_Join_toQ q)
     let b ← _root_.fast_pairing.canonical.Dot.push b (XRn_Join_toQ (eq v.c1)) (XRn_Join_toQ q)
     ok (some (a,b))

def finish : Option (Dot × Dot) → Result (Option C.E)
 | none => ok none
 | some (a,b) => do let out ← XSa_FinishPair.finish a b; ok (some out)

theorem same_step {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat) :
 oldStep sem s g point=XSa_OptionFold.absorb (step sem s g point) := by
 funext st l
 cases st with
 | none => rfl
 | some pair =>
   rcases pair with ⟨a,b⟩
   unfold oldStep XSa_OptionFold.absorb step
   apply (bind_eq_iff _ _ _).mpr
   intro q hq
   cases hv : XSa_CheckedQ.valid q <;> simp only [hv,Bool.not_false,Bool.not_true,if_true,if_false,Bool.false_eq_true]

theorem factor {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat) :
 XRn_Join_preparedPart (es sem) s g point =
 (do let state ← XSa_OptionFold.run (step sem s g point) (List.range 29) (XRn_Join_dotZero,XRn_Join_dotZero)
     finish state) := by
 rw [XSa_OptionFold.same,←same_step,XRy_ClaimPartFactor.factor]
 unfold oldStep finish XSa_FinishPair.finish
 simp only [bind_assoc_eq,bind_tc_ok]
 rfl

#print axioms same_step
#print axioms factor
end XSa_PartFold
