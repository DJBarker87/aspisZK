import PV_B1_258_Funs
import PV_B1_WordZero
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleEqual
open Aeneas Aeneas.Std Result PV_B1_258
abbrev Q := aspis_core.field.QM31

def difference (a b : Q) : U32 :=
  (((a.c0.a ^^^ b.c0.a) ||| (a.c0.b ^^^ b.c0.b)) |||
    (a.c1.a ^^^ b.c1.a)) ||| (a.c1.b ^^^ b.c1.b)

theorem source (a b : Q) : equal a b =
    ok (decide (difference a b = 0#u32)) := by
  simp only [equal,difference,lift,bind_tc_ok]
  apply congrArg Result.ok
  exact decide_eq_decide.mpr Iff.rfl

theorem zero (a b : Q) : difference a b = 0#u32 ↔ a=b := by
  rcases a with ⟨⟨a0,a1⟩,⟨a2,a3⟩⟩
  rcases b with ⟨⟨b0,b1⟩,⟨b2,b3⟩⟩
  simp only [difference,PV_B1_WordZero.or_zero,PV_B1_WordZero.xor_zero]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩
    cases h0; cases h1; cases h2; cases h3
    rfl
  · intro h
    cases h
    exact ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
theorem same_words (a : Q) : difference a a=0#u32 := (zero a a).mpr rfl
theorem zero_symmetric (a b : Q) : difference a b=0#u32 ↔ difference b a=0#u32 := by
  rw [zero,zero]
  exact eq_comm
theorem source_self (a : Q) : equal a a = ok true := by
  rw [source]
  simp only [same_words,decide_true]
theorem source_comm (a b : Q) :
    equal a b = equal b a := by
  rw [source,source]
  apply congrArg Result.ok
  exact decide_eq_decide.mpr (zero_symmetric a b)
#print axioms source_comm
#print axioms source_self
#print axioms zero_symmetric
#print axioms same_words
#print axioms source
#print axioms zero
end PV_B1_PoleEqual
