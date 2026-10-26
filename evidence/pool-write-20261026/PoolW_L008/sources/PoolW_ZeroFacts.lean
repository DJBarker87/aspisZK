import PoolW_ZeroExact
set_option autoImplicit false
namespace AspisR1.PoolW_ZeroFacts
open Aeneas Aeneas.Std Result

theorem accepted_iff (bytes : Slice U8) :
    PoolW_Zero.zero_bytes bytes = ok true ↔ ∀ byte ∈ bytes.val, byte = 0#u8 := by
  rw [PoolW_ZeroExact.exact]
  simp

theorem nonzero_rejects (bytes : Slice U8) (byte : U8)
    (member : byte ∈ bytes.val) (nonzero : byte ≠ 0#u8) :
    PoolW_Zero.zero_bytes bytes = ok false := by
  rw [PoolW_ZeroExact.exact]
  have notall : ¬ ∀ b ∈ bytes.val, b = 0#u8 := by
    intro all
    exact nonzero (all byte member)
  have allfalse : bytes.val.all (fun b => decide (b = 0#u8)) = false := by
    simpa using notall
  rw [allfalse]

#print axioms accepted_iff
#print axioms nonzero_rejects
end AspisR1.PoolW_ZeroFacts
