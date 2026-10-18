import R1Z.BatchedAlgebra

/-! D49.4 C2, the D34.3 line items (zf1/DESIGN-P-CERT.txt §2.3 RF-rel), Lean side.

* `storedFirstLineX18_eq_rustLineNode`: the stored line-18 node of
  `BatchedAlgebra.lineInverse` is the Rust `line_node(u) = 2·x(fibre_point u)² − 1`
  (z4/z9.rs:290-293; the production `fast_domain::line_node`), with the Rust
  `fibre_point(u)` modelled by `storedInitialFibrePoint20 u`.
* `lineInverse_zero_rust`, `lineInverse_one_rust`, `lineInverse_two_rust`
  (D34.3 item 2): the three entries of `lineInverse v` are the
  multipliers that `line_fold_with_inverses` applies to the `QueryGeometry`
  inverses of `(line_x, line_y, line_z)` (verifier.rs:171-207, 218-227 on
  origin/codex/100bit-spend-path-20261013, crates/aspis-r1-cost-probe):
  `half·ix`, `−half·iy` (the Rust uses `d − c`, the Lean fold `v 2 − v 3`), and
  `half·iz`.
* `rustLineFold_eq_lineFoldLinear`: the Rust fold formula with those inverses
  equals the Lean `lineFoldLinear` at `lineInverse v`, for every challenge and
  every four-symbol fibre.

The Rust side of the identifications (that the extracted `fibre_point`,
`line_node`, the batch inversion and the M31 constants compute these Lean
terms) is the C3 extraction job.  Nothing is evaluated over the 2^16 parents. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfLine

open AspisCircleGroupOrder

/-- Rust `M31(1073741824)` (z9.rs:309; verifier.rs:219). -/
def rustHalf : ZMod P := 1073741824

/-- Rust `weights::QUARTER = M31(536870912)` (aspis-r1-cost-probe weights.rs:5). -/
def rustQuarter : ZMod P := 536870912

theorem two_mul_rustHalf : (2 : ZMod P) * rustHalf = 1 := by
  have e : (2 : ZMod P) * rustHalf = ((P + 1 : ℕ) : ZMod P) := by
    unfold rustHalf
    rw [show P + 1 = 2 * 1073741824 by norm_num [P], Nat.cast_mul]
    norm_num
  rw [e, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem four_mul_rustQuarter : (4 : ZMod P) * rustQuarter = 1 := by
  have e : (4 : ZMod P) * rustQuarter = ((P + 1 : ℕ) : ZMod P) := by
    unfold rustQuarter
    rw [show P + 1 = 4 * 536870912 by norm_num [P], Nat.cast_mul]
    norm_num
  rw [e, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]

theorem rustHalf_eq_inv : rustHalf = (2 : ZMod P)⁻¹ :=
  eq_inv_of_mul_eq_one_right two_mul_rustHalf

theorem rustQuarter_eq : rustQuarter = rustHalf * rustHalf := by
  have h4 : rustQuarter = (4 : ZMod P)⁻¹ := eq_inv_of_mul_eq_one_right four_mul_rustQuarter
  rw [h4, rustHalf_eq_inv, ← mul_inv]
  norm_num

/-- Rust `line_node(u)` (z9.rs:290-293): `x = fibre_point(u).x`, `2x² − 1`. -/
def rustLineNode (u : Fin 262144) : ZMod P :=
  2 * (X (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 u)) ^ 2 - 1

/-- D34.3 item 1: `storedFirstLineX18` is the Rust `line_node` formula. -/
theorem storedFirstLineX18_eq_rustLineNode (u : Fin 262144) :
    AspisV7ExactOneFoldDomains.storedFirstLineX18 u = rustLineNode u := by
  rw [AspisV7ExactOneFoldDomains.storedFirstLineX18_eq_doubled]
  rfl

/-- `QueryGeometry::for_range` values for a query `u` with parent `v = u/4`
(verifier.rs:177-183): circle `x, y` of the query's fibre point (supplied),
then `line_x = line_node(4v)`, `line_y = line_node(4v+3)`, `line_z = 2·line_x² − 1`. -/
def qgValues (px py : ZMod P) (v : Fin 65536) : Fin 5 → ZMod P :=
  ![px, py, rustLineNode (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0),
    rustLineNode (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3),
    2 * rustLineNode (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2 - 1]

/-- The inverses `QueryGeometry` stores (verifier.rs:186-201: batch inversion of
the nonzero values; the batch-inversion algorithm is a C3 item). -/
def qgInverses (px py : ZMod P) (v : Fin 65536) : Fin 5 → ZMod P :=
  fun i => (qgValues px py v i)⁻¹

/-- D34.3 item 2 (entry 0). -/
theorem lineInverse_zero_rust (px py : ZMod P) (v : Fin 65536) :
    R1Z.BatchedAlgebra.lineInverse v 0 = rustHalf * qgInverses px py v 2 := by
  change (2 * AspisV7ExactOneFoldDomains.storedFirstLineX18
        (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0))⁻¹ =
      rustHalf * (rustLineNode (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0))⁻¹
  rw [storedFirstLineX18_eq_rustLineNode, mul_inv, rustHalf_eq_inv]

theorem lineInverse_one_rust (px py : ZMod P) (v : Fin 65536) :
    R1Z.BatchedAlgebra.lineInverse v 1 = -(rustHalf * qgInverses px py v 3) := by
  change -(2 * AspisV7ExactOneFoldDomains.storedFirstLineX18
        (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3))⁻¹ =
      -(rustHalf * (rustLineNode (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3))⁻¹)
  rw [storedFirstLineX18_eq_rustLineNode, mul_inv, rustHalf_eq_inv]

theorem lineInverse_two_rust (px py : ZMod P) (v : Fin 65536) :
    R1Z.BatchedAlgebra.lineInverse v 2 = rustHalf * qgInverses px py v 4 := by
  change (2 * (2 * AspisV7ExactOneFoldDomains.storedFirstLineX18
        (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2 - 1))⁻¹ =
      rustHalf * (2 * rustLineNode (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2 - 1)⁻¹
  rw [storedFirstLineX18_eq_rustLineNode, mul_inv, rustHalf_eq_inv]

section Fold

variable {K : Type*} [Field K] [Algebra (ZMod P) K]

/-- Rust `line_fold_with_inverses(alpha, [a,b,c,d], inverse)` (verifier.rs:218-227),
with `mul_m31` the base-field scalar action. -/
def rustLineFold (alpha : K) (a : Fin 4 → K) (inv : Fin 5 → ZMod P) : K :=
  let h0 := (a 0 + a 1 + a 2 + a 3) * algebraMap (ZMod P) K rustQuarter
  let h2 := (a 0 + a 1 - a 2 - a 3) * algebraMap (ZMod P) K (rustQuarter * inv 4)
  let c0 := (a 0 - a 1) * algebraMap (ZMod P) K (rustHalf * inv 2)
  let c1 := (a 3 - a 2) * algebraMap (ZMod P) K (rustHalf * inv 3)
  let h1 := (c0 + c1) * algebraMap (ZMod P) K rustHalf
  let h3 := (c0 - c1) * algebraMap (ZMod P) K (rustHalf * inv 4)
  h0 + alpha * (h1 + alpha * (h2 + alpha * h3))

theorem algebraMap_rustHalf : algebraMap (ZMod P) K rustHalf = (2 : K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (algebraMap (ZMod P) K) two_mul_rustHalf
  rwa [map_mul, map_one, map_ofNat] at h

/-- The Rust fold with the `QueryGeometry` inverses is the Lean line fold at
`lineInverse v` (the map `lineFoldLayer 65536 α lineInverse` applies at `v`). -/
theorem rustLineFold_eq_lineFoldLinear (alpha : K) (a : Fin 4 → K) (px py : ZMod P)
    (v : Fin 65536) :
    rustLineFold alpha a (qgInverses px py v) =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldLinear alpha
        (algebraMap (ZMod P) K (R1Z.BatchedAlgebra.lineInverse v 0))
        (algebraMap (ZMod P) K (R1Z.BatchedAlgebra.lineInverse v 1))
        (algebraMap (ZMod P) K (R1Z.BatchedAlgebra.lineInverse v 2)) a := by
  rw [lineInverse_zero_rust px py v, lineInverse_one_rust px py v,
    lineInverse_two_rust px py v,
    AspisV5ComponentCConcreteFoldLinearity.lineFoldLinear_apply,
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue_eq_polynomial]
  simp only [rustLineFold, AspisV5ComponentCConcreteFoldLinearity.lineFoldPolynomialValue,
    map_mul, map_neg, rustQuarter_eq, algebraMap_rustHalf, div_eq_mul_inv]
  ring

end Fold

#print axioms two_mul_rustHalf
#print axioms four_mul_rustQuarter
#print axioms rustQuarter_eq
#print axioms storedFirstLineX18_eq_rustLineNode
#print axioms lineInverse_zero_rust
#print axioms lineInverse_one_rust
#print axioms lineInverse_two_rust
#print axioms algebraMap_rustHalf
#print axioms rustLineFold_eq_lineFoldLinear

end R1Z.RfLine

end
