import KNA_Frame
set_option autoImplicit false
namespace KNA_LPe_K017
open KMX_CopyMeaning KMY_WindowComposition
theorem result (roots : Nat → Nat → Nat) (query before : Nat → Nat)
 (j : Nat) (bound : j<152) :
 2*32+22*4=152 ∧
 KMY_RootComposition.rootsQueries (fun b => roots (b/32) (b%32))
  (fun b => (query (b/4) / 2^(8*(b%4))) % 256) before j =
 if j<64 then roots (j/32) (j%32)
 else (query ((j-64)/4) / 2^(8*((j-64)%4))) % 256 := by
 constructor
 · exact KMY_RootComposition.roots_queries_length
 · exact KMY_RootComposition.roots_queries_bytes roots
     (fun i b => (query i / 2^(8*b)) % 256) before j bound
#print axioms result
end KNA_LPe_K017
