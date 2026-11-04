import NEV_QRawMaps
set_option autoImplicit false
noncomputable section
namespace NEV_QRawAtoms
open Aeneas Aeneas.Std Result
/-- Keep the large arithmetic body symbolic: identify the constant operand,
then apply the SAME checked-product continuation instead of evaluating PP. -/
theorem modulus : NEV_QRaw.fast_pairing.canonical.P=FIo_QRaw.canonical.P := by
  unfold NEV_QRaw.fast_pairing.canonical.P FIo_QRaw.canonical.P
  rfl

theorem pp : NEV_QRaw.fast_pairing.canonical.Q.raw.PP=FIo_QRaw.canonical.Q.raw.PP := by
  unfold NEV_QRaw.fast_pairing.canonical.Q.raw.PP FIo_QRaw.canonical.Q.raw.PP
  rw [modulus]

theorem read0 {T : Type} (a b c d : T) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=ok a := by rfl
theorem read1 {T : Type} (a b c d : T) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=ok b := by rfl
theorem read2 {T : Type} (a b c d : T) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=ok c := by rfl
theorem read3 {T : Type} (a b c d : T) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=ok d := by rfl
#print axioms modulus
#print axioms pp
#print axioms read0
#print axioms read1
#print axioms read2
#print axioms read3
end NEV_QRawAtoms
end
