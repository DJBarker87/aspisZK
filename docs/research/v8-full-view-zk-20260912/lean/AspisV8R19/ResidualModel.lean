/- Explicit low residual arithmetic. Ring-homomorphism transport will give an
   exact polynomial model, not a rank or shared-oracle probability premise. -/
import AspisV8R19.LowResidualFactor
import AspisV8R19.FactorLeading

namespace AspisR19.ResidualModel
open AspisV8R17
variable {F : Type*} [CommRing F]
noncomputable section

def xEntry (half : F) (j r : Nat) : F :=
  (((indexLoop 10 j 0).getD []).map fun e => if r=e.1 then half^e.2 else 0).sum

theorem xEntry_eq (half : F) (j r : Nat) : xEntry half j r=sparseX half j r := by
  have hw := weightedIndexLoop_powers half 10 j 0
  simp only [pow_zero] at hw
  unfold sparseX sparseVector
  rw [hw]
  cases he : indexLoop 10 j 0 <;> simp [xEntry,he,List.map_map,Function.comp_def]

def xxEntry (half : F) (j r : Nat) : F :=
  (((indexLoop 10 j 0).getD []).map fun e => half^e.2*xEntry half e.1 r).sum

theorem xxEntry_eq (half : F) (j r : Nat) : xxEntry half j r=sparseXX half j r := by
  have hw := weightedIndexLoop_powers half 10 j 0
  simp only [pow_zero] at hw
  unfold sparseXX
  rw [hw]
  cases he : indexLoop 10 j 0 <;> simp [xxEntry,he,List.map_map,Function.comp_def,xEntry_eq]

def delta (j r : Nat) : F := if r=j then 1 else 0
def chordEntry (half a b c : F) (j r : Nat) : F :=
  if j%2=0 then
    if r%2=0 then a*delta (j/2) (r/2)+b*xEntry half (j/2) (r/2)
    else c*delta (j/2) (r/2)
  else if r%2=0 then c*(delta (j/2) (r/2)-xxEntry half (j/2) (r/2))
    else a*delta (j/2) (r/2)+b*xEntry half (j/2) (r/2)

theorem chordEntry_eq (half a b c : F) (j r : Nat) (hj : j<1024) :
    chordEntry half a b c j r=sourceChord half (unitVector j) a b c r := by
  by_cases h : j%2=0
  · have he : j=2*(j/2) := by omega
    conv_rhs => rw [he]
    rw [sourceChord_unit_even half (j/2) r (by omega)]
    simp [chordEntry,h,delta,unitVector,xEntry_eq]
  · have he : j=2*(j/2)+1 := by omega
    conv_rhs => rw [he]
    rw [sourceChord_unit_odd half (j/2) r (by omega)]
    simp [chordEntry,h,delta,unitVector,xEntry_eq,xxEntry_eq]

def carry (z : Fin 10 → F) (i : Fin 10) : F :=
  ∏ k : Fin 10, if i.val<k.val then z k else 1
def point (z : Fin 10 → F) (which : Nat) (i : Fin 10) : F :=
  if which=0 then z i else if which=1 then z i+carry z i-2*z i*carry z i
  else if i.val=6 ∨ i.val=7 then 1-z i else z i
def tensor (z : Fin 10 → F) (r : Nat) : F :=
  ∏ i : Fin 10, if (r/2^(9-i.val))%2=0 then 1-z i else z i
def codeWeight (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (z : Fin 10 → F) (j : Fin 111) : F :=
  tensor z (order j)-(if inactive j then tensor z 1023 else 0)
def pointWeight (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half a b c : F) (z : Fin 10 → F) (which r : Nat) : F :=
  ∑ j : Fin 111, codeWeight order inactive (point z which) j*
    chordEntry half a b c r j.val

def shift (half : F) : Nat → (Fin 27 → F) → Fin 27 → F
  | 0,p,r => p r
  | n+1,p,r => ∑ j : Fin 27, shift half n p j*xEntry half j.val r.val
def quotient (half alpha : F) (p : Fin 23 → F) (col : Fin 13) (r : Fin 108) : F :=
  let v := shift half (col.val/3) (fun j => if h : j.val<23 then p ⟨j.val,h⟩ else 0)
    ⟨r.val/4,by have := r.isLt; omega⟩
  if r.val%4=0 then -(alpha^(col.val%3+1))*v
  else if r.val%4=col.val%3+1 then v else 0

def polyCoeff (quarter : F) (q w : Fin 108 → F) (k : Nat) : F :=
  ∑ block : Fin 27, ∑ a : Fin 4, ∑ b : Fin 4,
    if a.val+b.val=k then quarter*q ⟨4*block.val+a.val,by omega⟩*
      w ⟨4*block.val+(4-b.val)%4,by omega⟩ else 0

def observation (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half quarter a b c κ alpha : F) (z : Fin 10 → F) (p : Fin 23 → F)
    (row : Nat) (col : Fin 13) : F :=
  let q := quotient half alpha p col
  let e := fun which (r : Fin 108) => pointWeight order inactive half a b c z which r.val
  if row=0 then 0 else if row<3 then ∑ r, q r*e row r
  else if row<10 then polyCoeff quarter q
    (fun r => κ*e 0 r+κ^2*e 1 r+κ^3*e 2 r) (row-3)
  else polyCoeff quarter q (fun r => κ^2*e 1 r+κ^3*e 2 r) (row-10)

def selectedRow (i : Fin 13) : Nat := [1,2,3,4,5,6,7,8,10,11,12,13,15].getD i.val 0
def minor (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half quarter a b c κ alpha : F) (z : Fin 10 → F) (p : Fin 23 → F) :
    Matrix (Fin 13) (Fin 13) F := fun i j =>
  observation order inactive half quarter a b c κ alpha z p (selectedRow i) j

section Mapping
variable {G : Type*} [CommRing G] (f : F →+* G)
theorem map_xEntry (half : F) (j r : Nat) :
    f (xEntry half j r)=xEntry (f half) j r := by
  simp [xEntry,map_list_sum,List.map_map,Function.comp_def,apply_ite]
theorem map_xxEntry (half : F) (j r : Nat) :
    f (xxEntry half j r)=xxEntry (f half) j r := by
  simp [xxEntry,map_list_sum,List.map_map,Function.comp_def,map_xEntry]
theorem map_chordEntry (half a b c : F) (j r : Nat) :
    f (chordEntry half a b c j r)=chordEntry (f half) (f a) (f b) (f c) j r := by
  unfold chordEntry
  have hd (i r : Nat) : f (delta (F:=F) i r)=delta (F:=G) i r := by
    by_cases h : r=i <;> simp [delta,h]
  split_ifs <;> simp only [map_add,map_sub,map_mul,map_xEntry,map_xxEntry,hd]
theorem map_point (z : Fin 10 → F) (which : Nat) (i : Fin 10) :
    f (point z which i)=point (fun j => f (z j)) which i := by
  unfold point
  split_ifs <;> simp [carry,apply_ite,map_prod,map_ofNat]
theorem map_pointWeight (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half a b c : F) (z : Fin 10 → F) (which r : Nat) :
    f (pointWeight order inactive half a b c z which r)=
      pointWeight order inactive (f half) (f a) (f b) (f c) (fun j => f (z j)) which r := by
  simp [pointWeight,codeWeight,tensor,apply_ite,map_sum,map_prod,map_point,map_chordEntry]
theorem map_shift (half : F) (n : Nat) (p : Fin 27 → F) (r : Fin 27) :
    f (shift half n p r)=shift (f half) n (fun j => f (p j)) r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp [shift,map_sum,ih,map_xEntry]
theorem map_quotient (half alpha : F) (p : Fin 23 → F) (col : Fin 13) (r : Fin 108) :
    f (quotient half alpha p col r)=quotient (f half) (f alpha) (fun j => f (p j)) col r := by
  have hm (n : Nat) (r : Fin 27) :
      f (shift half n (fun j => if h : j.val<23 then p ⟨j.val,h⟩ else 0) r)=
      shift (f half) n (fun j => if h : j.val<23 then f (p ⟨j.val,h⟩) else 0) r := by
    rw [map_shift]
    congr 1
    funext j
    split_ifs <;> simp
  unfold quotient
  split_ifs <;> simp only [map_mul,map_neg,map_pow,map_zero,hm]
theorem map_polyCoeff (quarter : F) (q w : Fin 108 → F) (k : Nat) :
    f (polyCoeff quarter q w k)=polyCoeff (f quarter) (fun j => f (q j)) (fun j => f (w j)) k := by
  simp [polyCoeff,apply_ite,map_sum]
theorem map_observation (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
    (half quarter a b c κ alpha : F) (z : Fin 10 → F) (p : Fin 23 → F)
    (row : Nat) (col : Fin 13) :
    f (observation order inactive half quarter a b c κ alpha z p row col)=
      observation order inactive (f half) (f quarter) (f a) (f b) (f c) (f κ) (f alpha)
        (fun j => f (z j)) (fun j => f (p j)) row col := by
  unfold observation
  split_ifs <;> simp only [map_zero,map_sum,map_mul,map_add,map_pow,
    map_quotient,map_pointWeight,map_polyCoeff]
end Mapping

#print axioms xEntry_eq
#print axioms xxEntry_eq
#print axioms chordEntry_eq
#print axioms map_xEntry
#print axioms map_xxEntry
#print axioms map_chordEntry
#print axioms map_point
#print axioms map_pointWeight
#print axioms map_shift
#print axioms map_quotient
#print axioms map_polyCoeff
#print axioms map_observation
end
end AspisR19.ResidualModel
