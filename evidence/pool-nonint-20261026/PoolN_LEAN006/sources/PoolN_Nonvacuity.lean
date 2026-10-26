import PoolN_Effects
set_option autoImplicit false
namespace AspisR1.PoolN_Nonvacuity
open Aeneas Aeneas.Std PoolN_Guards PoolN_Effects

/-- An occupied ASC8 shape exists for every SDK metadata carrier. This is
mathematical guard consistency; native reachability is separately covered by
Kani. It does not claim that arbitrary data is a canonical authenticated ASC8. -/
theorem ASC8_shape (sdk : AdapterRw.Cuts.Account) (id : Key) :
    ∃ a : Account, a.data.length = 192 ∧ a.data.head? = some 65#u8 ∧
      prepared a id 10000 = .error .InvalidAccountData ∧
      prepared a id 8504 = .error .InvalidAccountData := by
  let a : Account := ⟨sdk,List.replicate 192 65#u8⟩
  have len : a.data.length = 192 := by simp [a]
  exact ⟨a,len,by simp [a],
    prepared_rejects a id 10000 (Or.inl len) (Or.inl rfl),
    prepared_rejects a id 8504 (Or.inl len) (Or.inr rfl)⟩

/-- The verifier CP is a different inhabited length/marker shape. -/
theorem CP_shape (sdk : AdapterRw.Cuts.Account) (id : Key) :
    ∃ a : Account, a.data.length = 1768 ∧ a.data.head? = some 82#u8 ∧
      prepared a id 10000 = .error .InvalidAccountData ∧
      prepared a id 8504 = .error .InvalidAccountData := by
  let a : Account := ⟨sdk,List.replicate 1768 82#u8⟩
  have len : a.data.length = 1768 := by simp [a]
  exact ⟨a,len,by simp [a],
    prepared_rejects a id 10000 (Or.inr len) (Or.inl rfl),
    prepared_rejects a id 8504 (Or.inr len) (Or.inr rfl)⟩

#print axioms ASC8_shape
#print axioms CP_shape
end AspisR1.PoolN_Nonvacuity
