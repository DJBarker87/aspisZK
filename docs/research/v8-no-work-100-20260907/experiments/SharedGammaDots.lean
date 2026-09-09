import SemanticCarry
import QmCrossRange
namespace AspisV8.SharedGammaDots
open AspisV8.AffinePrimal AspisV8.SemanticCarry
open scoped BigOperators
abbrev part := AspisV8.QmCross.partialFold
theorem four_product_prefix (n s a b : Nat) (hn:n<4)
    (hs:s≤n*m^2) (ha:a≤m) (hb:b≤m) :
    s+a*b≤(n+1)*m^2 ∧ (s+(a*b)%word)%word=s+a*b := by
  have hab:a*b≤m^2 := by simpa [pow_two] using Nat.mul_le_mul ha hb
  have hpost:s+a*b≤(n+1)*m^2 := by nlinarith
  have hw:s+a*b<word := by
    have hcap:(n+1)*m^2≤4*m^2 := Nat.mul_le_mul_right _ (by omega)
    have hbound:4*m^2<word := by norm_num [m,p,word]
    omega
  exact ⟨hpost,by rw [Nat.mod_eq_of_lt (show a*b<word by omega),Nat.mod_eq_of_lt hw]⟩
theorem outer_prefix (n s raw : Nat) (hn:n<7) (hs:s≤4*m+n*(5*p+3)) (hr:raw<word) :
    s+part raw≤4*m+(n+1)*(5*p+3) ∧
    (s+part raw)%word=s+part raw := by
  have hf:=AspisV8.QmCross.raw_partial_range raw hr
  change part raw<5*p+4 at hf
  have hpost:s+part raw≤4*m+(n+1)*(5*p+3) := by nlinarith
  have hw:s+part raw<word := by dsimp [m,p,word] at *;omega
  exact ⟨hpost,Nat.mod_eq_of_lt hw⟩
theorem partial_cast (raw : Nat) :
    (part raw:ZMod p)=(raw:ZMod p) := by
  calc
    (part raw:ZMod p)=((part raw%p:Nat):ZMod p) := by simp
    _ = ((raw%p:Nat):ZMod p) :=
      congrArg (fun x:Nat => (x:ZMod p)) (AspisV8.QmCross.partial_congr raw)
    _ = (raw:ZMod p) := by simp
def castC (s : C Nat) : C (ZMod p) := fun i j => (s i j:ZMod p)
def partialC (s : C Nat) : C Nat := fun i j => part (s i j)
theorem cast_partial_add (s t : C Nat) :
    castC (s+partialC t)=castC s+castC t := by
  funext i j
  simp only [castC,partialC,Pi.add_apply,Nat.cast_add,partial_cast]
theorem outer_cast (chunks : List (C Nat)) (seed : C Nat) :
    castC (chunks.foldl (fun s t => s+partialC t) seed)=
      chunks.foldl (fun s t => s+castC t) (castC seed) := by
  induction chunks generalizing seed with
  | nil => rfl
  | cons t ts ih => simp only [List.foldl_cons,ih,cast_partial_add]
variable {R : Type*} [CommRing R]
theorem groups_reconstruct (groups : List (List (Q R × Q R))) (seed : C R) :
    reconstruct (groups.foldl (fun s xs => xs.foldl (fun t xy => t+productChannels xy.1 xy.2) s) seed)=
      groups.foldl (fun s xs => xs.foldl (fun t xy => t+towerMul xy.1 xy.2) s) (reconstruct seed) := by
  induction groups generalizing seed with
  | nil => rfl
  | cons xs gs ih => simp only [List.foldl_cons,ih,accumulate_reconstructs]
theorem structural_unit (c : Q R) : towerMul ![1,0,0,0] c=c := by
  funext i
  fin_cases i <;> simp [towerMul]
theorem grouping (f : Nat → R) (n : Nat) :
    (∑ i∈Finset.range (4*n),f i)=
      ∑ g∈Finset.range n,∑ j∈Finset.range 4,f (4*g+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,
      Finset.sum_range_succ (fun g => ∑ j∈Finset.range 4,f (4*g+j)) n]
theorem source_indices (g j : Nat) (hg:g<7) (hj:j<4) :
    4*g+j<28 ∧ 1+4*g+j<29 ∧ (4*g+j)/4=g ∧ (4*g+j)%4=j := by omega

-- The literal canonical limb decomposition used before the raw u64 products.
def castQ (x : Q Nat) : Q (ZMod p) := fun i => (x i:ZMod p)
def partsN (x : Q Nat) : C Nat :=
  ![![x 0,x 1,(x 0+x 1)%p],![x 2,x 3,(x 2+x 3)%p],
    ![(x 0+x 2)%p,(x 1+x 3)%p,((x 0+x 2)%p+(x 1+x 3)%p)%p]]
def productsN (x y : Q Nat) : C Nat := fun i j => partsN x i j*partsN y i j
theorem canonical_parts (x : Q Nat) : castC (partsN x)=parts (castQ x) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [castC,partsN,parts,castQ]
theorem raw_product_cast (x y : Q Nat) :
    castC (productsN x y)=productChannels (castQ x) (castQ y) := by
  funext i j
  simp only [castC,productsN,Nat.cast_mul,productChannels]
  change castC (partsN x) i j*castC (partsN y) i j=_
  rw [canonical_parts,canonical_parts]
def rawGroup (xs : List (Q Nat × Q Nat)) : C Nat :=
  xs.foldl (fun s xy => s+productsN xy.1 xy.2) 0
theorem cast_raw_fold (xs : List (Q Nat × Q Nat)) (s : C Nat) :
    castC (xs.foldl (fun t xy => t+productsN xy.1 xy.2) s)=
      xs.foldl (fun t xy => t+productChannels (castQ xy.1) (castQ xy.2)) (castC s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons xy xs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    funext i j
    simp only [castC,Pi.add_apply,Nat.cast_add]
    change castC s i j+castC (productsN xy.1 xy.2) i j=_
    rw [raw_product_cast]
    rfl
theorem fold_seed {S T : Type*} [AddMonoid S] (f : T → S) (xs : List T) (s : S) :
    xs.foldl (fun a x => a+f x) s=s+xs.foldl (fun a x => a+f x) 0 := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,zero_add]
    rw [ih (s+f x),ih (f x),add_assoc]
theorem one_group (xs : List (Q Nat × Q Nat)) (s : C Nat) :
    reconstruct (castC (s+partialC (rawGroup xs)))=
      xs.foldl (fun t xy => t+towerMul (castQ xy.1) (castQ xy.2)) (reconstruct (castC s)) := by
  rw [cast_partial_add]
  have h0:castC (0:C Nat)=(0:C (ZMod p)) := by funext i j;simp [castC]
  rw [rawGroup,cast_raw_fold,h0]
  rw [←fold_seed]
  simpa only [List.foldl_map] using accumulate_reconstructs
    (xs.map (fun xy => (castQ xy.1,castQ xy.2))) (castC s)
theorem kernel_result (groups : List (List (Q Nat × Q Nat))) (s : C Nat) :
    reconstruct (castC (groups.foldl (fun t xs => t+partialC (rawGroup xs)) s))=
      groups.foldl (fun t xs => xs.foldl
        (fun u xy => u+towerMul (castQ xy.1) (castQ xy.2)) t) (reconstruct (castC s)) := by
  induction groups generalizing s with
  | nil => rfl
  | cons xs gs ih => simp only [List.foldl_cons,ih,one_group]
#print axioms four_product_prefix
#print axioms outer_prefix
#print axioms partial_cast
#print axioms cast_partial_add
#print axioms outer_cast
#print axioms groups_reconstruct
#print axioms structural_unit
#print axioms grouping
#print axioms source_indices
#print axioms canonical_parts
#print axioms raw_product_cast
#print axioms cast_raw_fold
#print axioms fold_seed
#print axioms one_group
#print axioms kernel_result
end AspisV8.SharedGammaDots
