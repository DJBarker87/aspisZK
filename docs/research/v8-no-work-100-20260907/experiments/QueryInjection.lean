import QueryAffine
namespace AspisV8.QueryInjection
open AspisV8.AffinePrimal AspisV8.SemanticCarry AspisV8.SharedGammaDots
open scoped BigOperators
variable {R : Type*} [CommRing R]
-- The old source emits a power, then multiplies even after the last emission.
def oldWalk (rho : R) : Nat → R → List R × R
  | 0,s => ([],s)
  | n+1,s => let tail:=oldWalk rho n (s*rho);(s::tail.1,tail.2)
-- The new source seeds its array and makes only the remaining n updates.
def seeded (rho : R) : Nat → R → List R
  | 0,s => [s]
  | n+1,s => s::seeded rho n (rho*s)
theorem emitted_scales_equal (rho s:R) (n:Nat) :
    (oldWalk rho (n+1) s).1=seeded rho n s := by
  induction n generalizing s with
  | zero => simp [oldWalk,seeded]
  | succ n ih =>
    change s::(oldWalk rho (n+1) (s*rho)).1=s::seeded rho n (rho*s)
    rw [ih]
    rw [mul_comm s rho]
theorem source22_scales (rho:R) : (oldWalk rho 22 rho).1=seeded rho 21 rho :=
  emitted_scales_equal rho rho 21
theorem old_walk_length (rho s:R) (n:Nat) : (oldWalk rho n s).1.length=n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [oldWalk,List.length_cons,ih]
def weighted (rho : R) : R → List R → R
  | _,[] => 0
  | s,v::vs => s*v+weighted rho (s*rho) vs
def horner (rho:R) : List R → R
  | [] => 0
  | v::vs => v+rho*horner rho vs
theorem weighted_factor (rho s:R) (vs:List R) :
    weighted rho s vs=s*horner rho vs := by
  induction vs generalizing s with
  | nil => simp [weighted,horner]
  | cons v vs ih => simp only [weighted,horner,ih];ring
theorem old_dot (rho s:R) (vs:List R) :
    (List.zipWith (·*·) (oldWalk rho vs.length s).1 vs).sum=weighted rho s vs := by
  induction vs generalizing s with
  | nil => simp [oldWalk,weighted]
  | cons v vs ih => simp [oldWalk,weighted,ih]
theorem shifted_dot22 (rho:R) (vs:List R) (hn:vs.length=22) :
    (List.zipWith (·*·) (seeded rho 21 rho) vs).sum=rho*horner rho vs := by
  rw [←source22_scales,←hn,old_dot,weighted_factor]
-- The pre-existing relation discrepancy stays the degree-zero coefficient.
theorem discrepancy (rho prior:R) (received expected:List R) :
    prior+(rho*horner rho received)-(rho*horner rho expected)=
      prior-rho*(horner rho expected-horner rho received) := by ring

def canonicalC (s:C Nat) : C Nat := fun i j => s i j%p
theorem cast_canonical (s:C Nat) : castC (canonicalC s)=castC s := by
  funext i j;simp [castC,canonicalC]
theorem cast_add (s t:C Nat) : castC (s+t)=castC s+castC t := by
  funext i j;simp [castC]
theorem canonical_group (s:C Nat) (xs:List (Q Nat × Q Nat)) :
    reconstruct (castC (s+canonicalC (rawGroup xs)))=
      xs.foldl (fun t xy => t+towerMul (castQ xy.1) (castQ xy.2)) (reconstruct (castC s)) := by
  rw [cast_add,cast_canonical,reconstruct_add,AspisV8.QueryAffine.helper_result,
    fold_seed (fun xy:Q Nat × Q Nat => towerMul (castQ xy.1) (castQ xy.2)) xs (reconstruct (castC s))]
theorem canonical_groups (s:C Nat) (groups:List (List (Q Nat × Q Nat))) :
    reconstruct (castC (groups.foldl (fun t xs => t+canonicalC (rawGroup xs)) s))=
      groups.foldl (fun t xs => xs.foldl (fun u xy => u+towerMul (castQ xy.1) (castQ xy.2)) t)
        (reconstruct (castC s)) := by
  induction groups generalizing s with
  | nil => rfl
  | cons xs groups ih => simp only [List.foldl_cons,ih,canonical_group]
-- Exact q22 long-dot schedule: one <=256-element outer window, six inner blocks.
def blockIndices : List (List Nat) :=
  [[0,1,2,3],[4,5,6,7],[8,9,10,11],[12,13,14,15],[16,17,18,19],[20,21]]
theorem block_indices_cover : blockIndices.flatten=List.range 22 := by decide
theorem block_lengths : blockIndices.map List.length=[4,4,4,4,4,2] := by decide
theorem raw_prefix (n s a b:Nat) (hn:n<4) (hs:s≤n*m^2) (ha:a≤m) (hb:b≤m) :
    s+a*b≤(n+1)*m^2 ∧ (s+(a*b)%word)%word=s+a*b :=
  four_product_prefix n s a b hn hs ha hb
theorem canonical_outer_prefix (n s raw:Nat) (hn:n<6) (hs:s≤n*m) :
    s+raw%p≤(n+1)*m ∧ (s+raw%p)%word=s+raw%p := by
  have hc:raw%p≤m := by
    have h:=Nat.mod_lt raw (show 0<p by norm_num [p]);dsimp [m];omega
  have hpost:s+raw%p≤(n+1)*m := by nlinarith
  have hw:s+raw%p<word := by dsimp [m,p,word] at *;omega
  exact ⟨hpost,Nat.mod_eq_of_lt hw⟩
theorem final_outer_reduction (s:C Nat) :
    reconstruct (castC (canonicalC s))=reconstruct (castC s) := by rw [cast_canonical]
theorem partial_outer_prefix (n s raw:Nat) (hn:n<6)
    (hs:s≤n*(5*p+3)) (hr:raw<word) :
    s+part raw≤(n+1)*(5*p+3) ∧ (s+part raw)%word=s+part raw := by
  have hc:=AspisV8.QmCross.raw_partial_range raw hr
  change part raw<5*p+4 at hc
  have hpost:s+part raw≤(n+1)*(5*p+3) := by nlinarith
  have hw:s+part raw<word := by dsimp [p,word] at *;omega
  exact ⟨hpost,Nat.mod_eq_of_lt hw⟩
theorem field_groups_flatten (s:Q (ZMod p)) (groups:List (List (Q Nat × Q Nat))) :
    groups.foldl (fun t xs => xs.foldl (fun u xy => u+towerMul (castQ xy.1) (castQ xy.2)) t) s=
      groups.flatten.foldl (fun u xy => u+towerMul (castQ xy.1) (castQ xy.2)) s := by
  induction groups generalizing s with
  | nil => rfl
  | cons xs groups ih => simp only [List.foldl_cons,List.flatten_cons,List.foldl_append,ih]
theorem fixed_partial_dot_result (groups:List (List (Q Nat × Q Nat))) :
    reconstruct (castC (groups.foldl (fun t xs => t+partialC (rawGroup xs)) 0))=
      groups.flatten.foldl (fun u xy => u+towerMul (castQ xy.1) (castQ xy.2)) 0 := by
  rw [kernel_result,field_groups_flatten]
  have hz:reconstruct (castC (0:C Nat))=(0:Q (ZMod p)) := by
    funext i;fin_cases i <;> simp [castC,reconstruct]
  rw [hz]
theorem shape_equivalence (log n xlen:Nat) :
    ¬(log=0 ∨ n=0 ∨ n≠xlen) ↔ log≠0 ∧ n≠0 ∧ n=xlen := by omega
theorem selected_inventory : 22>16 ∧ 22≤256 ∧ 22=5*4+2 ∧ 22-1=21 ∧
    6*9+9=63 ∧ 697*16+52+24+22*621+2*296*26=40282 := by norm_num
#print axioms emitted_scales_equal
#print axioms source22_scales
#print axioms old_walk_length
#print axioms weighted_factor
#print axioms old_dot
#print axioms shifted_dot22
#print axioms discrepancy
#print axioms cast_canonical
#print axioms cast_add
#print axioms canonical_group
#print axioms canonical_groups
#print axioms block_indices_cover
#print axioms block_lengths
#print axioms raw_prefix
#print axioms canonical_outer_prefix
#print axioms final_outer_reduction
#print axioms partial_outer_prefix
#print axioms field_groups_flatten
#print axioms fixed_partial_dot_result
#print axioms shape_equivalence
#print axioms selected_inventory
end AspisV8.QueryInjection
