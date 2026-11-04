import NFW_Transcript
set_option autoImplicit false
namespace AspisR1.NFW_TranscriptDomain
open Aeneas Aeneas.Std Result
/-- Exactly the six opening/rho rows reached by the two-fold constructor. -/
def calls : List (Nat × Nat) := [(27,928),(28,32),(29,224),(30,256),(31,2048),(32,0)]
theorem rows (row width : Nat) (inside : (row,width)∈calls) : row≤95 := by
 simp only [calls,List.mem_cons,List.not_mem_nil,or_false] at inside
 rcases inside with h|h|h|h|h|h <;> cases h <;> decide
theorem payloads (row width : Nat) (inside : (row,width)∈calls) : width≤2048 := by
 simp only [calls,List.mem_cons,List.not_mem_nil,or_false] at inside
 rcases inside with h|h|h|h|h|h <;> cases h <;> decide
theorem tag (row : U8) (bound : row.val≤95) :
 ∃ result,(160#u8+row : Result U8)=ok result ∧ result.val=160+row.val := by
 have spec : (160#u8+row : Result U8) ⦃ z => z.val=160+row.val ⦄ := by
  apply UScalar.add_spec
  scalar_tac
 exact WP.spec_imp_exists spec
#print axioms rows
#print axioms payloads
#print axioms tag
end AspisR1.NFW_TranscriptDomain
