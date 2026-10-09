import SelectedInitialOutputsSourcePolynomial

/-! Ring-generic algebra used by the selected projected Poseidon callback.

This file deliberately stops below the chronological source-polynomial
constructor.  It gives one definition of the two-round Poseidon predictions
which can be instantiated both in `QM31Exact` and coefficientwise in
`QM31Exact[X]`.  Thus the later slice proof does not compare an off-domain
formula with a Boolean-table MLE.

The matrices and the three selector classes are the mathematical form of
`state_only_poseidon::{external_linear_lazy,internal_linear_lazy,
leading_pair,interpolated_full_pair,interpolated_internal_pair}`.  Equality
with the optimized packed Rust machine kernels remains a separate refinement
obligation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedPoseidonGenericAlgebra

abbrev Base := AspisFormal.ArithmetizationCore.F
abbrev RC := AspisFormal.HashMerkleModel.RoundConstants

variable {R S : Type*} [CommRing R] [CommRing S]

abbrev State (R : Type*) := Fin 16 → R

def pow5 (x : R) : R := x ^ 5

/-- The literal 4-by-4 local external matrix followed by `J + I`. -/
def externalLinear (s : State R) : State R :=
  let m : State R :=
    ![ 2*s 0+3*s 1+s 2+s 3,   s 0+2*s 1+3*s 2+s 3,
       s 0+s 1+2*s 2+3*s 3,   3*s 0+s 1+s 2+2*s 3,
       2*s 4+3*s 5+s 6+s 7,   s 4+2*s 5+3*s 6+s 7,
       s 4+s 5+2*s 6+3*s 7,   3*s 4+s 5+s 6+2*s 7,
       2*s 8+3*s 9+s 10+s 11, s 8+2*s 9+3*s 10+s 11,
       s 8+s 9+2*s 10+3*s 11, 3*s 8+s 9+s 10+2*s 11,
       2*s 12+3*s 13+s 14+s 15, s 12+2*s 13+3*s 14+s 15,
       s 12+s 13+2*s 14+3*s 15, 3*s 12+s 13+s 14+2*s 15 ]
  let c0 := m 0 + m 4 + m 8 + m 12
  let c1 := m 1 + m 5 + m 9 + m 13
  let c2 := m 2 + m 6 + m 10 + m 14
  let c3 := m 3 + m 7 + m 11 + m 15
  ![ m 0+c0, m 1+c1, m 2+c2, m 3+c3,
     m 4+c0, m 5+c1, m 6+c2, m 7+c3,
     m 8+c0, m 9+c1, m 10+c2, m 11+c3,
     m 12+c0, m 13+c1, m 14+c2, m 15+c3 ]

/-- The literal width-16 internal matrix and pinned diagonal powers. -/
def internalLinear (s : State R) : State R :=
  let ps := s 1+s 2+s 3+s 4+s 5+s 6+s 7+s 8+s 9+s 10+s 11+s 12+s 13+s 14+s 15
  let full := ps + s 0
  ![ ps - s 0,
     full + s 1*1,     full + s 2*2,     full + s 3*4,
     full + s 4*8,     full + s 5*16,    full + s 6*32,
     full + s 7*64,    full + s 8*128,   full + s 9*256,
     full + s 10*1024, full + s 11*4096, full + s 12*8192,
     full + s 13*16384, full + s 14*32768, full + s 15*65536 ]

def fullRound (state constants : State R) : State R :=
  externalLinear (fun lane => pow5 (state lane + constants lane))

def internalRound (state : State R) (constant : R) : State R :=
  internalLinear (fun lane => if lane = 0 then pow5 (state lane + constant) else state lane)

def mapState (f : R →+* S) (state : State R) : State S := fun lane => f (state lane)

theorem externalLinear_map (f : R →+* S) (state : State R) :
    externalLinear (mapState f state) = mapState f (externalLinear state) := by
  funext lane
  fin_cases lane <;> simp [externalLinear, mapState, map_ofNat]

theorem internalLinear_map (f : R →+* S) (state : State R) :
    internalLinear (mapState f state) = mapState f (internalLinear state) := by
  funext lane
  fin_cases lane <;> simp [internalLinear, mapState, map_ofNat]

theorem fullRound_map (f : R →+* S) (state constants : State R) :
    fullRound (mapState f state) (mapState f constants) =
      mapState f (fullRound state constants) := by
  unfold fullRound
  have argument :
      (fun lane => pow5 (mapState f state lane + mapState f constants lane)) =
        mapState f (fun lane => pow5 (state lane + constants lane)) := by
    funext lane
    simp [mapState, pow5]
  rw [argument, externalLinear_map]

theorem internalRound_map (f : R →+* S) (state : State R) (constant : R) :
    internalRound (mapState f state) (f constant) =
      mapState f (internalRound state constant) := by
  unfold internalRound
  have argument :
      (fun lane => if lane = 0 then pow5 (mapState f state lane + f constant)
        else mapState f state lane) =
      mapState f (fun lane => if lane = 0 then pow5 (state lane + constant)
        else state lane) := by
    funext lane
    by_cases zero : lane = 0 <;> simp [zero, mapState, pow5]
  rw [argument, internalLinear_map]

/-- Constants for the three selected full/full local-row classes. -/
def fullEvenConstants (embed : Base →+* R) (rc : RC) (selector : Fin 16 → R) :
    State R := fun lane =>
  selector 1 * embed (rc.extInit 2 lane) +
    selector 9 * embed (rc.extFinal 0 lane) +
      selector 10 * embed (rc.extFinal 2 lane)

def fullOddConstants (embed : Base →+* R) (rc : RC) (selector : Fin 16 → R) :
    State R := fun lane =>
  selector 1 * embed (rc.extInit 3 lane) +
    selector 9 * embed (rc.extFinal 1 lane) +
      selector 10 * embed (rc.extFinal 3 lane)

/-- Constants for the seven selected internal/internal local-row classes. -/
def internalEvenConstant (embed : Base →+* R) (rc : RC)
    (selector : Fin 16 → R) : R :=
  ∑ row : Fin 7, selector ⟨row.val + 2, by omega⟩ * embed (rc.intern ⟨2 * row.val, by omega⟩)

def internalOddConstant (embed : Base →+* R) (rc : RC)
    (selector : Fin 16 → R) : R :=
  ∑ row : Fin 7, selector ⟨row.val + 2, by omega⟩ * embed (rc.intern ⟨2 * row.val + 1, by omega⟩)

def absorbRate (z xor12 : State R) : State R := fun lane =>
  if lane.val < 8 then z lane + xor12 lane else z lane

def leadingPrediction (embed : Base →+* R) (rc : RC)
    (z xor12 : State R) : State R :=
  fullRound
    (fullRound (externalLinear (absorbRate z xor12))
      (fun lane => embed (rc.extInit 0 lane)))
    (fun lane => embed (rc.extInit 1 lane))

def fullPrediction (embed : Base →+* R) (rc : RC)
    (z selector : State R) : State R :=
  fullRound (fullRound z (fullEvenConstants embed rc selector))
    (fullOddConstants embed rc selector)

def internalPrediction (embed : Base →+* R) (rc : RC)
    (z selector : State R) : State R :=
  internalRound (internalRound z (internalEvenConstant embed rc selector))
    (internalOddConstant embed rc selector)

def leadingWeight (selector : State R) : R := selector 0
def fullWeight (selector : State R) : R := selector 1 + selector 9 + selector 10
def internalWeight (selector : State R) : R :=
  ∑ row : Fin 7, selector ⟨row.val + 2, by omega⟩

/-- One unpacked residual coordinate of the exact three-difference projected
formula.  Packing is a separate linear operation. -/
def residualCoordinate (embed : Base →+* R) (rc : RC) (block : R)
    (selector z successor xor12 : State R) (lane : Fin 16) : R :=
  block *
    (leadingWeight selector * (successor lane - leadingPrediction embed rc z xor12 lane) +
      fullWeight selector * (successor lane - fullPrediction embed rc z selector lane) +
      internalWeight selector *
        (successor lane - internalPrediction embed rc z selector lane))

theorem fullEvenConstants_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (selector : State R) :
    fullEvenConstants embedS rc (mapState f selector) =
      mapState f (fullEvenConstants embedR rc selector) := by
  funext lane
  simp [fullEvenConstants, mapState, ← compatible]

theorem fullOddConstants_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (selector : State R) :
    fullOddConstants embedS rc (mapState f selector) =
      mapState f (fullOddConstants embedR rc selector) := by
  funext lane
  simp [fullOddConstants, mapState, ← compatible]

theorem internalEvenConstant_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (selector : State R) :
    internalEvenConstant embedS rc (mapState f selector) =
      f (internalEvenConstant embedR rc selector) := by
  simp [internalEvenConstant, mapState, ← compatible, map_sum]

theorem internalOddConstant_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (selector : State R) :
    internalOddConstant embedS rc (mapState f selector) =
      f (internalOddConstant embedR rc selector) := by
  simp [internalOddConstant, mapState, ← compatible, map_sum]

theorem absorbRate_map (f : R →+* S) (z xor12 : State R) :
    absorbRate (mapState f z) (mapState f xor12) =
      mapState f (absorbRate z xor12) := by
  funext lane
  by_cases rate : lane.val < 8 <;> simp [absorbRate, rate, mapState]

theorem leadingPrediction_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (z xor12 : State R) :
    leadingPrediction embedS rc (mapState f z) (mapState f xor12) =
      mapState f (leadingPrediction embedR rc z xor12) := by
  have constants0 :
      (fun lane => embedS (rc.extInit 0 lane)) =
        mapState f (fun lane => embedR (rc.extInit 0 lane)) := by
    funext lane
    exact DFunLike.congr_fun compatible (rc.extInit 0 lane) |>.symm
  have constants1 :
      (fun lane => embedS (rc.extInit 1 lane)) =
        mapState f (fun lane => embedR (rc.extInit 1 lane)) := by
    funext lane
    exact DFunLike.congr_fun compatible (rc.extInit 1 lane) |>.symm
  unfold leadingPrediction
  rw [constants0, constants1, absorbRate_map, externalLinear_map,
    fullRound_map, fullRound_map]

theorem fullPrediction_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (z selector : State R) :
    fullPrediction embedS rc (mapState f z) (mapState f selector) =
      mapState f (fullPrediction embedR rc z selector) := by
  unfold fullPrediction
  rw [fullEvenConstants_map f embedR embedS compatible,
    fullOddConstants_map f embedR embedS compatible,
    ← fullRound_map, ← fullRound_map]

theorem internalPrediction_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (z selector : State R) :
    internalPrediction embedS rc (mapState f z) (mapState f selector) =
      mapState f (internalPrediction embedR rc z selector) := by
  unfold internalPrediction
  rw [internalEvenConstant_map f embedR embedS compatible,
    internalOddConstant_map f embedR embedS compatible,
    ← internalRound_map, ← internalRound_map]

theorem leadingWeight_map (f : R →+* S) (selector : State R) :
    leadingWeight (mapState f selector) = f (leadingWeight selector) := rfl

theorem fullWeight_map (f : R →+* S) (selector : State R) :
    fullWeight (mapState f selector) = f (fullWeight selector) := by
  simp [fullWeight, mapState]

theorem internalWeight_map (f : R →+* S) (selector : State R) :
    internalWeight (mapState f selector) = f (internalWeight selector) := by
  simp [internalWeight, mapState, map_sum]

theorem residualCoordinate_map (f : R →+* S) (embedR : Base →+* R)
    (embedS : Base →+* S) (compatible : f.comp embedR = embedS)
    (rc : RC) (block : R) (selector z successor xor12 : State R)
    (lane : Fin 16) :
    residualCoordinate embedS rc (f block) (mapState f selector)
        (mapState f z) (mapState f successor) (mapState f xor12) lane =
      f (residualCoordinate embedR rc block selector z successor xor12 lane) := by
  simp only [residualCoordinate, leadingWeight_map, fullWeight_map,
    internalWeight_map, leadingPrediction_map f embedR embedS compatible,
    fullPrediction_map f embedR embedS compatible,
    internalPrediction_map f embedR embedS compatible, mapState,
    map_mul, map_add, map_sub]

#print axioms externalLinear_map
#print axioms internalLinear_map
#print axioms fullRound_map
#print axioms internalRound_map
#print axioms residualCoordinate_map
end AspisV8Completion.SelectedPoseidonGenericAlgebra
