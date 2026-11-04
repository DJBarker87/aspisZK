import KMX_CopyMeaning
set_option autoImplicit false
namespace AspisR1.NGC_FillInduction
/-- Fixed-value fill, one native resize/clone/push iteration at a time. -/
def run {T : Type} (value : T) : Nat→List T→List T
 | 0,before=>before
 | n+1,before=>run value n (before++[value])
theorem result {T : Type} (value : T) (n : Nat) (before : List T) :
 run value n before=before++List.replicate n value := by
 induction n generalizing before with
 | zero=>simp only [run,List.replicate_zero,List.append_nil]
 | succ n ih=>
  rw [run,ih]
  simp only [List.replicate_succ,List.append_assoc,List.singleton_append]
theorem empty {T : Type} (value : T) (n : Nat) :
 run value n []=List.replicate n value := by rw [result,List.nil_append]
theorem length {T : Type} (value : T) (n : Nat) (before : List T) :
 (run value n before).length=before.length+n := by rw [result,List.length_append,List.length_replicate]
theorem spare_capacity (initial n i cap : Nat) (bound : initial+n≤cap) (active : i<n) :
 initial+i<cap := by omega
#print axioms result
#print axioms empty
#print axioms length
#print axioms spare_capacity
end AspisR1.NGC_FillInduction
