import PV_L2C_InverseField
set_option autoImplicit false
namespace PV_L2C_InterpolationNodes
open scoped BigOperators
open PV_L2C_M31
local instance : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩

def node (i : Nat) : ZMod p := i

theorem distinct (i j : Nat) (hi : i < 28) (hj : j < 28) (he : i ≠ j) : node i ≠ node j := by
  intro h
  have hv := congrArg ZMod.val h
  simp only [node,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : i < p),
    Nat.mod_eq_of_lt (by omega : j < p)] at hv
  exact he hv
#print axioms distinct

def denominator (i n : Nat) : ZMod p :=
  ∏ j ∈ Finset.range n, if j=i then 1 else node i-node j

theorem nonzero (i n : Nat) (hi : i < 28) (hn : n ≤ 28) : denominator i n ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hj' : j < 28 := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
  split_ifs with he
  · exact one_ne_zero
  · exact sub_ne_zero.mpr (distinct i j hi hj' (Ne.symm he))
#print axioms nonzero
end PV_L2C_InterpolationNodes
