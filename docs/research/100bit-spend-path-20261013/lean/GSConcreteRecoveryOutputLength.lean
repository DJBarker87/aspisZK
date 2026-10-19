import GSConcreteRootRecovery
import RRFixedTapeRecoveryOutputLength

set_option autoImplicit false
namespace AspisR1.GSConcreteRootRecoveryOutputLength
open AspisR1.GSConcreteRootRecovery
open AspisR1.RRFixedTapeRecoveryOutputLength
open AspisR1.RRFixedTapeRecovery
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem initial_output_length_le_112 (q t : Nat) (points : Array (K × K))
    (hs : points.size = 1048576) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K)
    (cs : List (List K))
    (hout : initial q t points hs H = some cs) : cs.length ≤ 112 := by
  obtain ⟨Q, hr, _⟩ := GSConcreteInterpolation.initial_exists points hs
  have hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
  have hrecover :
      (recover 112 q t 1025 (GSConcreteInterpolation.initialState Q)
        hc.2.1 hc.2.2 H).1 = some cs := by
    rw [← initial_eq_recovery q t points hs Q hr H]
    exact hout
  exact recover_output_length_le 112 q t 1025 (GSConcreteInterpolation.initialState Q)
    hc.2.1 hc.2.2 hq H cs hrecover

theorem final_output_length_le_112 (q t : Nat) (points : Array (K × K))
    (hs : points.size = 262144) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K)
    (cs : List (List K))
    (hout : final q t points hs H = some cs) : cs.length ≤ 112 := by
  obtain ⟨Q, hr, _⟩ := GSConcreteInterpolation.final_exists points hs
  have hc := GSConcreteInterpolation.final_state_contract points hs Q hr
  have hrecover :
      (recover 112 q t 256 (GSConcreteInterpolation.finalState Q)
        hc.2.1 hc.2.2 H).1 = some cs := by
    rw [← final_eq_recovery q t points hs Q hr H]
    exact hout
  exact recover_output_length_le 112 q t 256 (GSConcreteInterpolation.finalState Q)
    hc.2.1 hc.2.2 hq H cs hrecover

#print axioms initial_output_length_le_112
#print axioms final_output_length_le_112
end AspisR1.GSConcreteRootRecoveryOutputLength
