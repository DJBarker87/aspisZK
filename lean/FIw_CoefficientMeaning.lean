import FIq_Native08
import FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CoefficientMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev Variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant

def scalar (v : Variant) (present : Bool) (input output transfer withdrawal : K) : List K :=
  [input, output + match v with
    | .PrivateTransfer => transfer
    | .Withdrawal => if present then withdrawal else 0]

/-- The last two installed semantic coefficients, on exactly the operands of
scalar_lanes. Earlier schedule/path/value/digest meanings remain separate. -/
theorem value (v : Variant) (present : Bool) (input output transfer withdrawal : NQ)
    (result : Array NQ 2#usize)
    (hi : Canon input) (ho : Canon output) (hp : Canon transfer) (hw : Canon withdrawal)
    (run : pool_v1.pair_forest_semantic_terminal.scalar_lanes v present
      input output transfer withdrawal=ok result) :
    (∀ x∈result.val,Canon x) ∧ result.val.map decode=
      scalar v present (decode input) (decode output) (decode transfer) (decode withdrawal) := by
  cases v with
  | PrivateTransfer =>
    unfold pool_v1.pair_forest_semantic_terminal.scalar_lanes at run
    obtain ⟨sum,hs,run⟩ := FIv_Map.bind_success _ _ _ run
    have value := FIv_NativeValue.add output transfer sum ho hp hs
    cases Result.ok.inj run
    constructor
    · intro x hx
      simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact value.1
    · simp only [Array.make,List.map_cons,List.map_nil,scalar,value.2]
  | Withdrawal =>
    cases present with
    | false =>
      cases Result.ok.inj run
      constructor
      · intro x hx
        simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact ho
      · simp only [Array.make,List.map_cons,List.map_nil,scalar,Bool.false_eq_true,
          ↓reduceIte,add_zero]
    | true =>
      unfold pool_v1.pair_forest_semantic_terminal.scalar_lanes at run
      obtain ⟨sum,hs,run⟩ := FIv_Map.bind_success _ _ _ run
      have value := FIv_NativeValue.add output withdrawal sum ho hw hs
      cases Result.ok.inj run
      constructor
      · intro x hx
        simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact value.1
      · simp only [Array.make,List.map_cons,List.map_nil,scalar,↓reduceIte,value.2]
#print axioms value
end AspisR1.FIw_CoefficientMeaning
end
