import AffinePrimal
namespace AspisV8.SemanticCarry
open AspisV8.AffinePrimal
variable {R : Type*} [CommRing R]
abbrev Q (R : Type*) := Fin 4 → R
abbrev C (R : Type*) := Fin 3 → Fin 3 → R
def parts (x : Q R) : C R :=
  ![![x 0,x 1,x 0+x 1],![x 2,x 3,x 2+x 3],
    ![x 0+x 2,x 1+x 3,(x 0+x 2)+(x 1+x 3)]]
def productChannels (x y : Q R) : C R := fun i j => parts x i j*parts y i j
def towerMul (x y : Q R) : Q R :=
  ![(x 0*y 0-x 1*y 1)+2*(x 2*y 2-x 3*y 3)-(x 2*y 3+x 3*y 2),
    (x 0*y 1+x 1*y 0)+(x 2*y 2-x 3*y 3)+2*(x 2*y 3+x 3*y 2),
    x 0*y 2-x 1*y 3+x 2*y 0-x 3*y 1,
    x 0*y 3+x 1*y 2+x 2*y 1+x 3*y 0]
theorem product_reconstructs (x y : Q R) :
    reconstruct (productChannels x y)=towerMul x y := by
  funext i
  fin_cases i <;> simp [reconstruct,productChannels,parts,towerMul] <;> ring
theorem reconstruct_add (s t : C R) :
    reconstruct (s+t)=reconstruct s+reconstruct t := by
  funext i
  fin_cases i <;> simp [reconstruct] <;> ring
theorem seeded_constant (a b c d : R) : reconstruct (inject 0 a b c d)=![a,b,c,d] := by
  rw [injected_constant]
  simp [reconstruct]
theorem accumulate_reconstructs (xs : List (Q R × Q R)) (s : C R) :
    reconstruct (xs.foldl (fun acc xy => acc+productChannels xy.1 xy.2) s) =
      xs.foldl (fun acc xy => acc+towerMul xy.1 xy.2) (reconstruct s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [List.foldl_cons,ih,reconstruct_add,product_reconstructs]

-- The source seeds the four offsets BEFORE at most four product updates.
theorem four_affine_ceiling : 4*m^2+4*m<word := by norm_num [m,p,word]
theorem seeded_mac {n s a b : Nat} (hn:n<4) (hs:s≤n*m^2+4*m)
    (ha:a≤m) (hb:b≤m) :
    (s+(a*b)%word)%word=s+a*b ∧ s+a*b≤(n+1)*m^2+4*m := by
  have hab:a*b≤m^2 := by simpa [pow_two] using Nat.mul_le_mul ha hb
  have hpost:s+a*b≤(n+1)*m^2+4*m := by nlinarith
  have hcap:(n+1)*m^2+4*m≤4*m^2+4*m := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (show n+1≤4 by omega)) _
  have hw:s+a*b<word := lt_of_le_of_lt (hpost.trans hcap) four_affine_ceiling
  rw [Nat.mod_eq_of_lt (show a*b<word by omega),Nat.mod_eq_of_lt hw]
  exact ⟨rfl,hpost⟩
theorem four_not_five : word<5*m^2 := by norm_num [m,p,word]

def oldStep (a acc c0 c1 c2 c3 : R) := a^4*acc+c0+(a*c1+a^2*c2+a^3*c3)
def fusedStep (a acc c0 c1 c2 c3 : R) := c0+(a*c1+a^2*c2+a^3*c3+a^4*acc)
theorem step_identity (a acc c0 c1 c2 c3 : R) :
    fusedStep a acc c0 c1 c2 c3=oldStep a acc c0 c1 c2 c3 := by
  dsimp [oldStep,fusedStep]
  ring
theorem all_blocks (a init : R) (blocks : List (Q R)) :
    blocks.foldl (fun acc c => fusedStep a acc (c 0) (c 1) (c 2) (c 3)) init =
      blocks.foldl (fun acc c => oldStep a acc (c 0) (c 1) (c 2) (c 3)) init := by
  simp only [step_identity]
theorem first_block (a c0 c1 c2 c3 : R) :
    fusedStep a 0 c0 c1 c2 c3=c0+(a*c1+a^2*c2+a^3*c3) := by simp [fusedStep]
#print axioms product_reconstructs
#print axioms reconstruct_add
#print axioms seeded_constant
#print axioms accumulate_reconstructs
#print axioms four_affine_ceiling
#print axioms seeded_mac
#print axioms four_not_five
#print axioms step_identity
#print axioms all_blocks
#print axioms first_block
end AspisV8.SemanticCarry
