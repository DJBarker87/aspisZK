import PV_L2C_NativeQ
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace PV_L2C_SampleCanonical
open PV_L2C_M31 PV_L2C_NativeQ
/-- The literal m31 control on an arbitrary supplied raw-word stream. Failed
prefixes are retained by the surrounding L2B trace laws, not assigned a law here. -/
def scan : Nat → List word → Option (word × List word)
 | 0,_ => none
 | _+1,[] => none
 | n+1,w::ws =>
   let c := w &&& BitVec.ofNat 32 p
   if c.toNat<p then some (c,ws) else scan n ws

theorem scalar_canonical (fuel : Nat) (xs : List word) (v : word) (rest : List word)
    (h : scan fuel xs=some (v,rest)) : canonical v := by
  induction fuel generalizing xs with
  | zero => simp [scan] at h
  | succ n ih =>
    cases xs with
    | nil => simp [scan] at h
    | cons w ws =>
      unfold scan at h
      dsimp only at h
      split at h
      · rename_i hc
        have he := congrArg Prod.fst (Option.some.inj h)
        exact he ▸ hc
      · exact ih ws h
#print axioms scalar_canonical

def tuple (a b c d : word) : Q := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then c else d

theorem tuple_canonical (a b c d : word)
    (ha : canonical a) (hb : canonical b) (hc : canonical c) (hd : canonical d) :
    Canonical (tuple a b c d) := by
  intro i
  fin_cases i <;> simp [tuple,ha,hb,hc,hd]
#print axioms tuple_canonical

def sampleQ (fuel : Nat) (xs : List word) : Option (Q × List word) :=
 match scan fuel xs with
 | none => none
 | some (a,xs1) =>
   match scan fuel xs1 with
   | none => none
   | some (b,xs2) =>
     match scan fuel xs2 with
     | none => none
     | some (c,xs3) =>
       match scan fuel xs3 with
       | none => none
       | some (d,xs4) => some (tuple a b c d,xs4)

theorem secure_canonical (fuel : Nat) (xs : List word) (q : Q) (rest : List word)
    (h : sampleQ fuel xs=some (q,rest)) : Canonical q := by
  unfold sampleQ at h
  cases h0 : scan fuel xs with
  | none => simp [h0] at h
  | some av =>
    rcases av with ⟨a,xs1⟩
    cases h1 : scan fuel xs1 with
    | none => simp [h0,h1] at h
    | some bv =>
      rcases bv with ⟨b,xs2⟩
      cases h2 : scan fuel xs2 with
      | none => simp [h0,h1,h2] at h
      | some cv =>
        rcases cv with ⟨c,xs3⟩
        cases h3 : scan fuel xs3 with
        | none => simp [h0,h1,h2,h3] at h
        | some dv =>
          rcases dv with ⟨d,xs4⟩
          simp only [h0,h1,h2,h3,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
          have he : tuple a b c d=q := h.1
          rw [← he]
          exact tuple_canonical a b c d (scalar_canonical fuel xs a xs1 h0)
            (scalar_canonical fuel xs1 b xs2 h1) (scalar_canonical fuel xs2 c xs3 h2)
            (scalar_canonical fuel xs3 d xs4 h3)
#print axioms secure_canonical
end PV_L2C_SampleCanonical
