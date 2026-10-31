import PV_B3Q_PanicGuards
namespace PV_B3Q_ExpandGuards
set_option autoImplicit false
/-- The invariant of Selectors::expand before each coordinate. -/
def Stage (start coordinate len : Nat) : Prop :=
 start ≤ coordinate ∧ len = 2 ^ (coordinate - start)
theorem initial (start : Nat) : Stage start start 1 := by
 simp only [Stage,Nat.sub_self,pow_zero,le_refl,and_self]
theorem advance (start coordinate len : Nat) (invariant : Stage start coordinate len) :
 Stage start (coordinate+1) (len*2) := by
 rcases invariant with ⟨order,length⟩
 constructor
 · omega
 · rw [length,show coordinate + 1 - start = (coordinate-start)+1 by omega,pow_succ]
/-- Six high coordinates have capacities 1,2,4,8,16,32 before writing.
This is six tiny symbolic stages; no field term is reduced. -/
theorem high_stage_capacity (k : Nat) (guard : k < 6) : 2 * 2^k ≤ 64 := by
 have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
 rcases cases with h|h|h|h|h|h <;> subst k <;> decide
theorem low_stage_capacity (k : Nat) (guard : k < 4) : 2 * 2^k ≤ 16 := by
 have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
 rcases cases with h|h|h|h <;> subst k <;> decide
/-- Instantiation at the actual high-array caller. All three reads/writes in
the reverse inner loop are bounded before any field operation executes. -/
theorem high_inner (coordinate len index : Nat)
    (invariant : Stage 0 coordinate len) (outer : coordinate < 6)
    (inner : index < len) :
 coordinate < 10 ∧ index < 64 ∧ 2*index < 64 ∧ 2*index+1 < 64 := by
 have capacity := high_stage_capacity coordinate outer
 have same : len = 2^coordinate := by simpa [Stage] using invariant.2
 rw [←same] at capacity
 have writes := PV_B3Q_PanicGuards.expand_write_bounds index len 64 inner capacity
 exact ⟨by omega,writes⟩
/-- The low-array caller starts at six and visits four coordinates. -/
theorem low_inner (coordinate len index : Nat)
    (invariant : Stage 6 coordinate len) (outer : coordinate < 10)
    (inner : index < len) :
 coordinate < 10 ∧ index < 16 ∧ 2*index < 16 ∧ 2*index+1 < 16 := by
 have k : coordinate-6 < 4 := by omega
 have capacity := low_stage_capacity (coordinate-6) k
 rw [←invariant.2] at capacity
 exact ⟨outer,PV_B3Q_PanicGuards.expand_write_bounds index len 16 inner capacity⟩
#print axioms initial
#print axioms advance
#print axioms high_stage_capacity
#print axioms low_stage_capacity
#print axioms high_inner
#print axioms low_inner
end PV_B3Q_ExpandGuards
