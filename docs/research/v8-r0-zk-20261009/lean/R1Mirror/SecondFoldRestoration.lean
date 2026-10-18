import R1Mirror.ConcreteProjection

/-! Concrete restoration of one more radix-four layer above the existing
log-16 exact encoder. This is an encoder identity only; it makes no claim
about runtime verification, source correspondence, transcripts, or security.
-/

set_option autoImplicit false
noncomputable section

namespace AspisR1.SecondFoldRestoration

open scoped BigOperators
open AspisCircleGroupOrder AspisCircleTensorBinding
open AspisV5FriReleasedLineGeometry AspisV7ExactOneFoldDomains
open AspisV5FriConcreteEncoderApplicability AspisV5FriConcreteEncoderCommutation
open AspisWide.FinalEncoder

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

abbrev FinalWord (K : Type) := Fin 262144 → K
abbrev ParentWord (K : Type) := Fin 65536 → K
abbrev SmallMessage (K : Type) := Fin 64 → K
abbrev FinalMessage (K : Type) := Fin 256 → K

/-- The actual embedded log-18 radix-four geometry over the log-16 domain. -/
def x0 (i : Fin 65536) : K :=
  algebraMap (ZMod P) K (storedFirstLineX18 (AspisR1.childIndex i 0))

def x1 (i : Fin 65536) : K :=
  algebraMap (ZMod P) K (storedFirstLineX18 (AspisR1.childIndex i 2))

def x2 (i : Fin 65536) : K :=
  algebraMap (ZMod P) K (storedLine17X (binaryChildIndex i))

theorem concreteGeometry : AspisV5FriConcreteEncoderApplicability.Radix4LineGeometry
    (fun k => algebraMap (ZMod P) K (storedFirstLineX18 k))
    (fun i => algebraMap (ZMod P) K (storedLine16X i))
    x0 x1 x2 :=
  AspisR1.storedLine18_radix4_geometry_algebraMap K

private theorem map_eq_zero_iff {K : Type} [Field K]
    [Algebra (ZMod P) K] (z : ZMod P) :
    algebraMap (ZMod P) K z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    exact FaithfulSMul.algebraMap_injective (ZMod P) K (by simpa using hz)
  · rintro rfl
    simp

private theorem map_doubledFactor {K : Type*} [Field K]
    [Algebra (ZMod P) K] (x y : ZMod P)
    (h : AspisCircleTensorBinding.doubledFactor x 1 = y) :
    AspisCircleTensorBinding.doubledFactor (algebraMap (ZMod P) K x) 1 =
      algebraMap (ZMod P) K y := by
  have hm := congrArg (algebraMap (ZMod P) K) h
  simpa [AspisCircleTensorBinding.doubledFactor, map_sub, map_mul,
    map_pow, map_one, map_ofNat] using hm

/-- The first coordinate cannot vanish: its opposite stored slot would then
collide with it, contradicting injectivity of the released stored domain. -/
theorem x0_ne_zero (i : Fin 65536) : x0 (K := K) i ≠ (0 : K) := by
  intro hx
  have hbase : storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0) = 0 := by
    exact (map_eq_zero_iff (K := K)
      (storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0))).mp
      (by simpa [x0, AspisR1.childIndex,
        AspisV5ComponentCConcreteFoldLinearity.childIndex] using hx)
  have hneg := AspisR1.storedLine18_slot1 i
  have hslot : storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex i 1) = 0 := by
    rw [hneg, hbase]
    simp
  have heq : AspisV5ComponentCConcreteFoldLinearity.childIndex i 0 =
      AspisV5ComponentCConcreteFoldLinearity.childIndex i 1 :=
    storedFirstLineX18_injective (hbase.trans hslot.symm)
  have hval := congrArg Fin.val heq
  simp [AspisV5ComponentCConcreteFoldLinearity.childIndex] at hval

/-- The second inner coordinate cannot vanish, by the same stored-slot
collision argument on slots two and three. -/
theorem x1_ne_zero (i : Fin 65536) : x1 (K := K) i ≠ (0 : K) := by
  intro hx
  have hbase : storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex i 2) = 0 := by
    exact (map_eq_zero_iff (K := K)
      (storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex i 2))).mp
      (by simpa [x1, AspisR1.childIndex,
        AspisV5ComponentCConcreteFoldLinearity.childIndex] using hx)
  have hneg := AspisR1.storedLine18_slot3 i
  have hslot : storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex i 3) = 0 := by
    rw [hneg, hbase]
    simp
  have heq : AspisV5ComponentCConcreteFoldLinearity.childIndex i 2 =
      AspisV5ComponentCConcreteFoldLinearity.childIndex i 3 :=
    storedFirstLineX18_injective (hbase.trans hslot.symm)
  have hval := congrArg Fin.val heq
  simp [AspisV5ComponentCConcreteFoldLinearity.childIndex] at hval

/-- The outer coordinate is also nonzero. A zero doubled coordinate would
make the two inner coordinates equal up to sign, again colliding distinct
stored slots. -/
theorem x2_ne_zero (i : Fin 65536) : x2 (K := K) i ≠ (0 : K) := by
  intro hx2
  have h0 : 2 * (x0 (K := K) i) ^ 2 - 1 = 0 := by
    have h := map_doubledFactor (K := K)
      (storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0))
      (storedLine17X (binaryChildIndex i)) (AspisR1.storedLine18_t2_slot0 i)
    change AspisCircleTensorBinding.doubledFactor (x0 i) 1 = x2 i at h
    simp only [AspisCircleTensorBinding.doubledFactor] at h
    rw [hx2] at h
    exact h
  have h1 : 2 * (x1 (K := K) i) ^ 2 - 1 = 0 := by
    have h := map_doubledFactor (K := K)
      (storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex i 2))
      (-storedLine17X (binaryChildIndex i)) (AspisR1.storedLine18_t2_slot2 i)
    have h' : AspisCircleTensorBinding.doubledFactor (x1 (K := K) i) 1 =
        -x2 (K := K) i := by
      simpa [x1, x2, AspisR1.childIndex,
        AspisV5ComponentCConcreteFoldLinearity.childIndex, map_neg] using h
    simp only [AspisCircleTensorBinding.doubledFactor] at h'
    rw [hx2] at h'
    simpa using h'
  have htwo : (2 : K) ≠ 0 := AspisWide.InitialEncoder.two_ne_zero
  have heqmul : 2 * (x0 (K := K) i) ^ 2 =
      2 * (x1 (K := K) i) ^ 2 := by
    have h := congrArg (fun z : K => z + 1) (h0.trans h1.symm)
    simpa using h
  have hsquares : (x0 (K := K) i)^2 = (x1 (K := K) i)^2 := by
    exact mul_left_cancel₀ htwo heqmul
  have hfac : (x0 (K := K) i - x1 (K := K) i) *
      (x0 (K := K) i + x1 (K := K) i) = 0 := by
    calc
      (x0 (K := K) i - x1 (K := K) i) *
          (x0 (K := K) i + x1 (K := K) i) =
        (x0 (K := K) i)^2 - (x1 (K := K) i)^2 := by ring
      _ = 0 := by rw [hsquares]; ring
  rcases mul_eq_zero.mp hfac with heq | heq
  · have hcoords : x0 (K := K) i = x1 (K := K) i := sub_eq_zero.mp heq
    have hidx0 : AspisV5ComponentCConcreteFoldLinearity.childIndex i 0 =
        AspisR1.childIndex i 0 := by
      apply Fin.ext
      rfl
    have hidx2 : AspisV5ComponentCConcreteFoldLinearity.childIndex i 2 =
        AspisR1.childIndex i 2 := by
      apply Fin.ext
      rfl
    have hpoint := AspisR1.storedLine18_child_slot i 0
    have hpoint2 := AspisR1.storedLine18_child_slot i 2
    have heqbase : storedFirstLineX18
          (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0) =
        storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex i 2) := by
      have hmap :
          algebraMap (ZMod P) K
              (storedFirstLineX18
                (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0)) =
            algebraMap (ZMod P) K
              (storedFirstLineX18
                (AspisV5ComponentCConcreteFoldLinearity.childIndex i 2)) := by
        have hm := congrArg (algebraMap (ZMod P) K) hpoint
        have hm2 := congrArg (algebraMap (ZMod P) K) hpoint2
        rw [hidx0, hidx2] at hm hm2
        have hm0' : algebraMap (ZMod P) K
            (storedFirstLineX18
              (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0)) =
            AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
              (x0 i) (x1 i) 0 := by
          simpa [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint,
            x0, x1, hidx0, hidx2] using hm
        have hm2' : AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
            (x0 i) (x1 i) 2 =
            algebraMap (ZMod P) K
              (storedFirstLineX18
                (AspisV5ComponentCConcreteFoldLinearity.childIndex i 2)) := by
          simpa [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint,
            x0, x1, hidx0, hidx2] using hm2.symm
        calc
          _ = AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
                (x0 i) (x1 i) 0 := hm0'
          _ = AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
                (x0 i) (x1 i) 2 := by
            simp [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint, hcoords]
          _ = _ := hm2'
      exact FaithfulSMul.algebraMap_injective (ZMod P) K hmap
    have hidx := storedFirstLineX18_injective heqbase
    have hval := congrArg Fin.val hidx
    simp [AspisV5ComponentCConcreteFoldLinearity.childIndex] at hval
  · have hcoords : x0 (K := K) i = -x1 (K := K) i :=
      (eq_neg_iff_add_eq_zero).2 heq
    have hidx0 : AspisV5ComponentCConcreteFoldLinearity.childIndex i 0 =
        AspisR1.childIndex i 0 := by
      apply Fin.ext
      rfl
    have hidx2 : AspisV5ComponentCConcreteFoldLinearity.childIndex i 2 =
        AspisR1.childIndex i 2 := by
      apply Fin.ext
      rfl
    have hidx3 : AspisV5ComponentCConcreteFoldLinearity.childIndex i 3 =
        AspisR1.childIndex i 3 := by
      apply Fin.ext
      rfl
    have hpoint := AspisR1.storedLine18_child_slot i 0
    have hpoint3 := AspisR1.storedLine18_child_slot i 3
    have heqbase : storedFirstLineX18
          (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0) =
        storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex i 3) := by
      have hmap :
          algebraMap (ZMod P) K
              (storedFirstLineX18
                (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0)) =
            algebraMap (ZMod P) K
              (storedFirstLineX18
                (AspisV5ComponentCConcreteFoldLinearity.childIndex i 3)) := by
        have hm := congrArg (algebraMap (ZMod P) K) hpoint
        have hm3 := congrArg (algebraMap (ZMod P) K) hpoint3
        rw [hidx0, hidx2] at hm
        rw [hidx0, hidx2, hidx3] at hm3
        have hm0' : algebraMap (ZMod P) K
            (storedFirstLineX18
              (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0)) =
            AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
              (x0 i) (x1 i) 0 := by
          simpa [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint,
            x0, x1, hidx0, hidx2] using hm
        have hm3' : AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
            (x0 i) (x1 i) 3 =
            algebraMap (ZMod P) K
              (storedFirstLineX18
                (AspisV5ComponentCConcreteFoldLinearity.childIndex i 3)) := by
          simpa [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint,
            x0, x1, hidx0, hidx2, hidx3] using hm3.symm
        calc
          _ = AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
                (x0 i) (x1 i) 0 := hm0'
          _ = AspisV5FriConcreteEncoderApplicability.radix4ChildPoint
                (x0 i) (x1 i) 3 := by
            simp [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint,
              map_neg, hcoords]
          _ = _ := hm3'
      exact FaithfulSMul.algebraMap_injective (ZMod P) K hmap
    have hidx := storedFirstLineX18_injective heqbase
    have hval := congrArg Fin.val hidx
    simp [AspisV5ComponentCConcreteFoldLinearity.childIndex] at hval

def inverse0 (i : Fin 65536) : K := (2 * x0 (K := K) i)⁻¹
def inverse1 (i : Fin 65536) : K := (2 * x1 (K := K) i)⁻¹
def inverse2 (i : Fin 65536) : K := (2 * x2 (K := K) i)⁻¹

theorem inverse_products (i : Fin 65536) :
    2 * x0 (K := K) i * inverse0 i = 1 ∧
    2 * x1 (K := K) i * inverse1 i = 1 ∧
    2 * x2 (K := K) i * inverse2 i = 1 := by
  have htwo : (2 : K) ≠ 0 := AspisWide.InitialEncoder.two_ne_zero
  have h0 : 2 * x0 (K := K) i ≠ 0 := mul_ne_zero htwo (x0_ne_zero i)
  have h1 : 2 * x1 (K := K) i ≠ 0 := mul_ne_zero htwo (x1_ne_zero i)
  have h2 : 2 * x2 (K := K) i ≠ 0 := mul_ne_zero htwo (x2_ne_zero i)
  constructor
  · simpa [inverse0] using mul_inv_cancel₀ h0
  constructor
  · simpa [inverse1] using mul_inv_cancel₀ h1
  · simpa [inverse2] using mul_inv_cancel₀ h2

def transform (i : Fin 65536) (v : Fin 4 → K) : Fin 4 → K :=
  AspisV5FriConcreteEncoderCommutation.radix4Decode
    (inverse0 i) (inverse1 i) (inverse2 i) v

def channels (V : FinalWord K) : Fin 4 → ParentWord K :=
  fun s i => transform i (fun t => V (AspisR1.childIndex i t)) s

def foldWord (alpha : K) (V : FinalWord K) : ParentWord K :=
  fun i => AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue alpha
    (fun s => channels V s i)

def join (b : Fin 4 → SmallMessage K) : Fin (4 * 64) → K :=
  fun k => b (AspisV5FriConcreteEncoderCommutation.slotIndex (n := 64) k)
    (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 64) k)

def foldMessage (alpha : K) (b : Fin 4 → SmallMessage K) : SmallMessage K :=
  AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 alpha (join b)

theorem lane_join (b : Fin 4 → SmallMessage K) (s : Fin 4) :
    AspisV5FriConcreteEncoderCommutation.coefficientLane 64 s (join b) = b s := by
  funext i
  simp [AspisV5FriConcreteEncoderCommutation.coefficientLane, join]

theorem fold_join (alpha : K) (b : Fin 4 → SmallMessage K) :
    foldMessage alpha b =
      fun i => AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue alpha
        (fun s => b s i) := by
  funext i
  change AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue alpha
      (fun s => join b
        (AspisV5ComponentCConcreteFoldLinearity.childIndex i s)) = _
  have hp (s : Fin 4) :
      AspisV5FriConcreteEncoderCommutation.parentIndex
          (AspisV5ComponentCConcreteFoldLinearity.childIndex i s) = i := by
    apply Fin.ext
    simp [AspisV5FriConcreteEncoderCommutation.parentIndex,
      AspisV5ComponentCConcreteFoldLinearity.childIndex_val]
    omega
  have hs (s : Fin 4) :
      AspisV5FriConcreteEncoderCommutation.slotIndex
          (AspisV5ComponentCConcreteFoldLinearity.childIndex i s) = s := by
    apply Fin.ext
    simp [AspisV5FriConcreteEncoderCommutation.slotIndex,
      AspisV5ComponentCConcreteFoldLinearity.childIndex_val]
  simp [AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue, join, hp, hs]

private noncomputable def secondEncoderLinear :
    SmallMessage K →ₗ[K] ParentWord K where
  toFun := AspisR1.ConcreteProjection.secondEncoder
  map_add' a b := by
    funext i
    simp [AspisR1.ConcreteProjection.secondEncoder, AspisR1.naturalEval,
      add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext i
    simp only [AspisR1.ConcreteProjection.secondEncoder, AspisR1.naturalEval,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

private theorem secondEncoderLinear_eq_eval (a : SmallMessage K) (i : Fin 65536) :
    secondEncoderLinear a i =
      (naturalCoefficientPolynomial a).eval
        (algebraMap (ZMod P) K (storedLine16X i)) := by
  change AspisR1.naturalEval a _ = _
  rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
  rfl

/-- The deployed four values are represented by decoding and re-evaluating the
four decoded channels; both inverse identities are exact for the concrete
nonzero stored geometry. -/
theorem channel_decode_evaluate (V : FinalWord K) (i : Fin 65536) :
    AspisV5FriConcreteEncoderCommutation.radix4Evaluate
        (x0 i) (x1 i) (x2 i) (fun s => channels V s i) =
      fun t => V (AspisR1.childIndex i t) := by
  have hp := inverse_products (K := K) i
  exact AspisV5FriConcreteEncoderCommutation.radix4Evaluate_radix4Decode
    (x0 i) (x1 i) (x2 i) (inverse0 i) (inverse1 i) (inverse2 i)
    hp.1 hp.2.1 hp.2.2 (fun t => V (AspisR1.childIndex i t))

/-- Conversely, decoding an encoded fibre returns its four coefficient
channels, using the other exact radix-four inverse identity. -/
theorem channel_encode_decode (c : Fin 4 → K) (i : Fin 65536) :
    transform i (AspisV5FriConcreteEncoderCommutation.radix4Evaluate
      (x0 i) (x1 i) (x2 i) c) = c := by
  have hp := inverse_products (K := K) i
  exact AspisV5FriConcreteEncoderCommutation.radix4Decode_radix4Evaluate
    (x0 i) (x1 i) (x2 i) (inverse0 i) (inverse1 i) (inverse2 i)
    hp.1 hp.2.1 hp.2.2 c

private theorem exactFinal_join_radix4 (b : Fin 4 → SmallMessage K)
    (k : Fin 262144) :
    exactFinalEncoder (join b) k =
      AspisV5FriConcreteEncoderCommutation.radix4Evaluate
        (x0 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (x1 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (x2 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (fun s => secondEncoderLinear (b s)
          (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (AspisV5FriConcreteEncoderCommutation.slotIndex (n := 65536) k) := by
  let encoder := secondEncoderLinear (K := K)
  let parentPoint : Fin 65536 → K :=
    fun i => algebraMap (ZMod P) K (storedLine16X i)
  let childPoint : Fin 262144 → K :=
    fun i => algebraMap (ZMod P) K (storedFirstLineX18 i)
  have hLift := AspisV5FriConcreteEncoderApplicability.radix4LiftEncoder_eq_natural_eval
    (K := K) (n := 64) (m := 65536) (by norm_num)
    encoder parentPoint x0 x1 x2 childPoint
    (by
      intro message i
      exact secondEncoderLinear_eq_eval (K := K) message i)
    (concreteGeometry (K := K)) (join b) k
  have hExact := AspisR1.ConcreteProjection.exactFinal_eq_naturalEval
    (K := K) (join b) k
  have hpoly : (naturalCoefficientPolynomial (join b)).eval
      (algebraMap (ZMod P) K (storedFirstLineX18 k)) =
        AspisR1.naturalEval (join b)
          (algebraMap (ZMod P) K (storedFirstLineX18 k)) := by
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    rfl
  calc
    exactFinalEncoder (join b) k = AspisR1.naturalEval (join b)
        (algebraMap (ZMod P) K (storedFirstLineX18 k)) := hExact
    _ = (naturalCoefficientPolynomial (join b)).eval
        (algebraMap (ZMod P) K (storedFirstLineX18 k)) := hpoly.symm
    _ = AspisV5FriConcreteEncoderCommutation.radix4LiftEncoder
        encoder x0 x1 x2 (join b) k := hLift.symm
    _ = AspisV5FriConcreteEncoderCommutation.radix4Evaluate
        (x0 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (x1 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (x2 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (fun s => secondEncoderLinear (b s)
          (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
        (AspisV5FriConcreteEncoderCommutation.slotIndex (n := 65536) k) := by
      rw [← AspisV5FriConcreteEncoderCommutation.childIndex_parentIndex_slotIndex
        (n := 65536) k]
      rw [AspisV5FriConcreteEncoderCommutation.radix4LiftEncoder_apply_child]
      simp only [AspisV5FriConcreteEncoderCommutation.parentIndex_childIndex,
        AspisV5FriConcreteEncoderCommutation.slotIndex_childIndex]
      have hvec :
          (fun lane : Fin 4 => encoder
            (AspisV5FriConcreteEncoderCommutation.coefficientLane 64 lane (join b))
            (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k)) =
          (fun lane => secondEncoderLinear (b lane)
            (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k)) := by
        funext lane
        rw [lane_join]
      exact congrArg (fun v : Fin 4 → K =>
        AspisV5FriConcreteEncoderCommutation.radix4Evaluate
          (x0 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
          (x1 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k))
          (x2 (AspisV5FriConcreteEncoderCommutation.parentIndex (n := 65536) k)) v
          (AspisV5FriConcreteEncoderCommutation.slotIndex (n := 65536) k)) hvec

/-- Restoration on every complete stored quartet: if the decoded channels
agree with the four actual log-16 encodings on a parent support, the original
word agrees there with the exact log-18 encoding of their joined message. -/
theorem secondFoldRestoration (V : FinalWord K)
    (S : Finset (Fin 65536)) (b : Fin 4 → SmallMessage K)
    (hchannels : ∀ i ∈ S, ∀ s : Fin 4,
      channels V s i = AspisR1.ConcreteProjection.secondEncoder (b s) i) :
    ∀ k ∈ AspisR1.fullQuartetSet S,
      V k = exactFinalEncoder (join b) k := by
  intro k hk
  have hi := AspisR1.parentIndex_mem_of_mem_fullQuartetSet S hk
  let i := AspisV5FriConcreteEncoderCommutation.parentIndex k
  let s := AspisV5FriConcreteEncoderCommutation.slotIndex (n := 65536) k
  have hchannels_i : ∀ t : Fin 4,
      channels V t i = secondEncoderLinear (b t) i := by
    intro t
    simpa [i, secondEncoderLinear] using hchannels i hi t
  have hvalue := channel_decode_evaluate (K := K) V i
  have hslot := congrFun hvalue s
  calc
    V k = V (AspisR1.childIndex i s) := by
      have hidx : AspisR1.childIndex i s = k := by
        apply Fin.ext
        simp [i, s, AspisR1.childIndex,
          AspisV5FriConcreteEncoderCommutation.parentIndex,
          AspisV5FriConcreteEncoderCommutation.slotIndex]
        omega
      rw [hidx]
    _ = AspisV5FriConcreteEncoderCommutation.radix4Evaluate
          (x0 i) (x1 i) (x2 i) (fun t => channels V t i) s := hslot.symm
    _ = AspisV5FriConcreteEncoderCommutation.radix4Evaluate
          (x0 i) (x1 i) (x2 i) (fun t => secondEncoderLinear (b t) i) s := by
      congr 2
      funext t
      exact hchannels_i t
    _ = exactFinalEncoder (join b) k := by
      rw [exactFinal_join_radix4 (K := K) b k]

#print axioms x0_ne_zero
#print axioms x1_ne_zero
#print axioms x2_ne_zero
#print axioms inverse_products
#print axioms channel_decode_evaluate
#print axioms channel_encode_decode
#print axioms lane_join
#print axioms fold_join
#print axioms secondFoldRestoration

end AspisR1.SecondFoldRestoration
end
