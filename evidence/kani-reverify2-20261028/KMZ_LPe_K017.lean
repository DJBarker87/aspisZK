import KMZ_Growth
set_option autoImplicit false
namespace KMZ_LPe_K017
open KMX_CopyMeaning KMY_WindowComposition
theorem result (roots query : Nat → Nat → Nat) (before : Nat → Nat) (j : Nat) (bound : j<152) :
 KMY_RootComposition.rootsQueries (fun b => roots (b/32) (b%32)) (fun b => query (b/4) (b%4)) before j =
 if j<64 then roots (j/32) (j%32) else query ((j-64)/4) ((j-64)%4) :=
 KMY_RootComposition.roots_queries_bytes roots query before j bound
#print axioms result
end KMZ_LPe_K017
