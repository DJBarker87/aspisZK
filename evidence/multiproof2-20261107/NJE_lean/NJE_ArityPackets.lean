import NJA_CohortArity
import NJA_Context

set_option autoImplicit false
namespace NJE_ArityPackets
open Aeneas Aeneas.Std Result
open NJA_Multiproof

-- Complete source and adopted Result, on BOTH constructors, under any continuation.
-- No verifier acceptance, batch bound, sortedness, or child-result hypothesis.
theorem TX1_118 {α : Type} (a : multiproof.Arity) (k : U32 → Result α) :
    multiproof.Arity.bits a = AspisR1Stage2.multiproof.Arity.bits (NJA_CohortArity.arity a) ∧
    (do let b ← multiproof.Arity.bits a; k b) =
      k (match a with | .Two => 1#u32 | .Eight => 3#u32) := by
  constructor
  · exact NJA_CohortArity.bits a
  · cases a <;> rfl

theorem TX2_084 {α : Type} (a : multiproof.Arity) (k : U32 → Result α) :
    multiproof.Arity.bits a = AspisR1Stage2.multiproof.Arity.bits (NJA_CohortArity.arity a) ∧
    (do let b ← multiproof.Arity.bits a; k b) =
      k (match a with | .Two => 1#u32 | .Eight => 3#u32) := TX1_118 a k

theorem TX1_119 {α : Type} (a : multiproof.Arity) (k : U32 → Result α) :
    multiproof.Arity.levels a = AspisR1Stage2.multiproof.Arity.levels (NJA_CohortArity.arity a) ∧
    (do let b ← multiproof.Arity.levels a; k b) =
      k (match a with | .Two => 18#u32 | .Eight => 6#u32) := by
  constructor
  · exact NJA_CohortArity.levels a
  · cases a
    · rw [NJA_Arity.two_levels]; rfl
    · rw [NJA_Arity.eight_levels]; rfl

theorem TX2_085 {α : Type} (a : multiproof.Arity) (k : U32 → Result α) :
    multiproof.Arity.levels a = AspisR1Stage2.multiproof.Arity.levels (NJA_CohortArity.arity a) ∧
    (do let b ← multiproof.Arity.levels a; k b) =
      k (match a with | .Two => 18#u32 | .Eight => 6#u32) := TX1_119 a k

theorem TX1_120 {α : Type} (a : multiproof.Arity) (k : Usize → Result α) :
    multiproof.Arity.width a = AspisR1Stage2.multiproof.Arity.width (NJA_CohortArity.arity a) ∧
    (do let b ← multiproof.Arity.width a; k b) =
      k (match a with | .Two => 2#usize | .Eight => 8#usize) := by
  constructor
  · exact NJA_CohortArity.width a
  · cases a
    · rw [NJA_Arity.two_width]; rfl
    · rw [NJA_Arity.eight_width]; rfl

theorem TX2_086 {α : Type} (a : multiproof.Arity) (k : Usize → Result α) :
    multiproof.Arity.width a = AspisR1Stage2.multiproof.Arity.width (NJA_CohortArity.arity a) ∧
    (do let b ← multiproof.Arity.width a; k b) =
      k (match a with | .Two => 2#usize | .Eight => 8#usize) := TX1_120 a k

#print TX1_118
#print axioms TX1_118
#print TX2_084
#print axioms TX2_084
#print TX1_119
#print axioms TX1_119
#print TX2_085
#print axioms TX2_085
#print TX1_120
#print axioms TX1_120
#print TX2_086
#print axioms TX2_086
end NJE_ArityPackets
