import PositiveTerminalInsertion

/-! The transfer-only source lanes 92/93 are asset differences supported on
rows 44 and 508/460. Lane 94 adds the product-inverse residual at row 1014.
This leaf proves concrete tower separation on base-field Boolean residuals,
and the stronger structural separation at row 1014. It does not identify
last-pack zero with acceptance, nor treat arbitrary off-domain QM31 inputs
as four independent QM31 basis coordinates. Rust selector-array and machine
arithmetic translations remain outside this source-shaped field proof. -/
set_option autoImplicit false
namespace AspisV8.PositivePackBinding
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositiveTerminalInsertion
open AspisPool.V7PairForestCuArithmeticEquivalences
open scoped BigOperators

/-- Literal nested constructor used by lift_m31, with no chosen basis. -/
def liftBase (a : M31Exact) : QM31Exact := ⟨⟨a,0⟩,0⟩

theorem liftBase_zero : liftBase 0=0 := rfl
theorem liftBase_one : liftBase 1=1 := rfl
theorem liftBase_add (a b : M31Exact) :
    liftBase (a+b)=liftBase a+liftBase b := rfl
theorem liftBase_sub (a b : M31Exact) :
    liftBase (a-b)=liftBase a-liftBase b := by
  ext <;> simp [liftBase]
theorem liftBase_mul (a b : M31Exact) :
    liftBase (a*b)=liftBase a*liftBase b := by
  ext <;> simp [liftBase]

/-- Reuses the literal full-QM31 packer, then specialises only its inputs.
The four output coordinates are obtained, not hypothesised independent. -/
theorem literalPack_base_coordinates (v : Fin 4 → M31Exact) :
    literalPack (fun i=>liftBase (v i))=
      (⟨⟨v 0,v 1⟩,⟨v 2,v 3⟩⟩ : QM31Exact) := by
  ext <;> simp [literalPack,liftBase]

theorem base_pack_zero_iff (a b p : M31Exact) :
    literalPack ![liftBase a,liftBase b,liftBase p,0]=0 ↔
      a=0 ∧ b=0 ∧ p=0 := by
  have hp : literalPack ![liftBase a,liftBase b,liftBase p,0]=
      (⟨⟨a,b⟩,⟨p,0⟩⟩ : QM31Exact) := by
    have hv : (fun i=>liftBase ((![a,b,p,0] : Fin 4 → M31Exact) i))=
        ![liftBase a,liftBase b,liftBase p,0] := by
      funext i
      fin_cases i <;> rfl
    simpa [hv] using literalPack_base_coordinates ![a,b,p,0]
  rw [hp]
  constructor
  · intro h
    exact ⟨congrArg (fun x : QM31Exact=>x.re.re) h,
      congrArg (fun x : QM31Exact=>x.re.im) h,
      congrArg (fun x : QM31Exact=>x.im.re) h⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

/-- Each Boolean row uses the same most-significant-bit-first convention
as the selected high[6]/low[4] expansion and the new selector loop. -/
def rowBits (row : Nat) (i : Fin 10) : Bool := row.testBit (9-i.val)
def boolValue {K : Type*} [Zero K] [One K] (b : Bool) : K := if b then 1 else 0
def bitWeight {K : Type*} [Ring K] (target point : Bool) : K :=
  if target then boolValue point else 1-boolValue point
def booleanSelector {K : Type*} [CommRing K] {n : Nat}
    (target point : Fin n → Bool) : K := ∏ i,bitWeight (target i) (point i)
def rowSelector {K : Type*} [CommRing K] (target row : Nat) : K :=
  booleanSelector (rowBits target) (rowBits row)

theorem selector_self {K : Type*} [CommRing K] {n : Nat}
    (point : Fin n → Bool) : booleanSelector (K:=K) point point=1 := by
  apply Finset.prod_eq_one
  intro i _
  cases point i <;> simp [bitWeight,boolValue]

theorem selector_mismatch {K : Type*} [CommRing K] {n : Nat}
    (target point : Fin n → Bool) (i : Fin n) (h : target i≠point i) :
    booleanSelector (K:=K) target point=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases ht : target i <;> cases hp : point i <;>
    simp_all [bitWeight,boolValue]

theorem liftBase_selector {n : Nat} (target point : Fin n → Bool) :
    liftBase (booleanSelector (K:=M31Exact) target point)=
      booleanSelector (K:=QM31Exact) target point := by
  have bit (a b : Bool) : liftBase (bitWeight (K:=M31Exact) a b)=
      bitWeight (K:=QM31Exact) a b := by
    cases a <;> cases b <;> simp [bitWeight,boolValue,liftBase_zero,liftBase_one]
  have prod (s : Finset (Fin n)) :
      liftBase (∏ i ∈ s,bitWeight (K:=M31Exact) (target i) (point i))=
      ∏ i ∈ s,bitWeight (K:=QM31Exact) (target i) (point i) := by
    induction s using Finset.induction_on with
    | empty => simp [liftBase_one]
    | @insert i s hi ih => simp only [Finset.prod_insert hi,liftBase_mul,bit,ih]
  exact prod Finset.univ

theorem row1014_selector_separation :
    rowSelector (K:=QM31Exact) 44 1014=0 ∧
    rowSelector (K:=QM31Exact) 508 1014=0 ∧
    rowSelector (K:=QM31Exact) 460 1014=0 ∧
    rowSelector (K:=QM31Exact) 1014 1014=1 := by
  refine ⟨selector_mismatch _ _ (0 : Fin 10) ?_,
    selector_mismatch _ _ (0 : Fin 10) ?_,
    selector_mismatch _ _ (0 : Fin 10) ?_,selector_self _⟩ <;>
    decide

/-- Exact transfer scalar-lane formulas plus the opt-in new lane. The old
source has no lambda, chi, H/G, theta or mu input in either scalar lane. -/
def sourceLastPack (row : Nat) (asset publicAsset r c inv : QM31Exact) : QM31Exact :=
  literalPack ![
    rowSelector 44 row*(asset-publicAsset),
    (rowSelector 508 row+rowSelector 460 row)*(asset-publicAsset),
    rowSelector 1014 row*(r*c*inv-1),0]

/-- Concrete base-valued inputs suffice at every Boolean row; old residuals
are not assumed zero. The source's lift and field operations are derived. -/
theorem source_base_pack_zero_iff (row : Nat) (asset publicAsset r c inv : M31Exact) :
    sourceLastPack row (liftBase asset) (liftBase publicAsset)
      (liftBase r) (liftBase c) (liftBase inv)=0 ↔
    rowSelector (K:=M31Exact) 44 row*(asset-publicAsset)=0 ∧
    (rowSelector (K:=M31Exact) 508 row+rowSelector 460 row)*(asset-publicAsset)=0 ∧
    rowSelector (K:=M31Exact) 1014 row*(r*c*inv-1)=0 := by
  have liftrow (target : Nat) : liftBase (rowSelector (K:=M31Exact) target row)=
      rowSelector (K:=QM31Exact) target row := liftBase_selector _ _
  have h:=base_pack_zero_iff
    (rowSelector (K:=M31Exact) 44 row*(asset-publicAsset))
    ((rowSelector (K:=M31Exact) 508 row+rowSelector 460 row)*(asset-publicAsset))
    (rowSelector (K:=M31Exact) 1014 row*(r*c*inv-1))
  simpa only [sourceLastPack,liftBase_mul,liftBase_sub,liftBase_add,
    liftBase_one,liftrow] using h

theorem towerU_ne_zero : towerU≠0 := by
  intro h
  have hz:=congrArg (fun x : QM31Exact=>x.im.re) h
  exact one_ne_zero hz

/-- At the reserved row the old assets disappear by public selector
structure, even when the supplied field values are arbitrary QM31. -/
theorem row1014_last_pack (asset publicAsset r c inv : QM31Exact) :
    sourceLastPack 1014 asset publicAsset r c inv=towerU*(r*c*inv-1) := by
  rcases row1014_selector_separation with ⟨h44,h508,h460,h1014⟩
  simp only [sourceLastPack,h44,h508,h460,h1014,zero_mul,zero_add,one_mul]
  exact literalPack_slot2 _

theorem row1014_pack_binding (asset publicAsset r c inv : QM31Exact) :
    sourceLastPack 1014 asset publicAsset r c inv=0 ↔ r*c*inv=1 := by
  rw [row1014_last_pack,mul_eq_zero]
  simp only [towerU_ne_zero,false_or,sub_eq_zero]

/-- Regression: without Boolean/base-field structure four extension-valued
slots are not independent. Never use the base-coordinate theorem on OOD
claims merely because their wire elements are canonical QM31. -/
theorem arbitrary_extension_cancellation (w : QM31Exact) :
    literalPack ![-(towerU*w),0,w,0]=0 := by
  rw [literalPack_eq_tower_map]
  simp [packBase4]

#print axioms liftBase_mul
#print axioms literalPack_base_coordinates
#print axioms base_pack_zero_iff
#print axioms selector_self
#print axioms selector_mismatch
#print axioms liftBase_selector
#print axioms row1014_selector_separation
#print axioms source_base_pack_zero_iff
#print axioms row1014_last_pack
#print axioms row1014_pack_binding
#print axioms arbitrary_extension_cancellation
end AspisV8.PositivePackBinding
