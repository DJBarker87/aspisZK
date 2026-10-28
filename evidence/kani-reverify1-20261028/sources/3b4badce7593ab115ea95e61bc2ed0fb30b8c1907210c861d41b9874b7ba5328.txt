import KMY_VectorComposition
set_option autoImplicit false
namespace KMY_RootComposition
open KMY_WindowComposition

def rootsQueries (roots query before : Nat → Nat) : Nat → Nat :=
  windows (fun b => query (b-64)) (windows roots before 0 32 2) 64 4 22

theorem roots_queries (roots query before : Nat → Nat) (j : Nat) (bound : j<152) :
    rootsQueries roots query before j = if j<64 then roots j else query (j-64) := by
  simp only [rootsQueries, windows_spec]
  by_cases h : j<64
  · have a : ¬ (64 ≤ j ∧ j < 64+4*22) := by omega
    have b : 0 ≤ j ∧ j < 0+32*2 := by omega
    simp only [if_neg a, if_pos b, if_pos h]
  · have a : 64 ≤ j ∧ j < 64+4*22 := by omega
    simp only [if_pos a, if_neg h]

theorem roots_queries_bytes (roots query : Nat → Nat → Nat) (before : Nat → Nat)
    (j : Nat) (bound : j<152) :
    rootsQueries (fun b => roots (b/32) (b%32))
      (fun b => query (b/4) (b%4)) before j =
      if j<64 then roots (j/32) (j%32) else query ((j-64)/4) ((j-64)%4) :=
  roots_queries _ _ _ j bound

theorem roots_queries_length : 2*32+22*4=152 := rfl

#print axioms roots_queries
#print axioms roots_queries_bytes
#print axioms roots_queries_length
end KMY_RootComposition
