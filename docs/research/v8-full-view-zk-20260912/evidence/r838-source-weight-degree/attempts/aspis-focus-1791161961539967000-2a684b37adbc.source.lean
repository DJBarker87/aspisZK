import AspisV8R19.R742SourceObservationHom
import AspisV8R19.R745JointObservationPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

set_option autoImplicit false
namespace AspisV8R19.R838SourceWeightDegree
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R745JointObservationPolynomial
noncomputable section
variable {F : Type*} [CommRing F]

abbrev Poly := JointPoly F

lemma list_sum_degree_le {xs : List Poly} {D : Nat}
    (hxs : ∀ x ∈ xs, x.totalDegree ≤ D) : xs.sum.totalDegree ≤ D := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons]
      apply (totalDegree_add _ _).trans
      apply max_le
      · exact hxs x (by simp)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

lemma constant_pow_degree_le (half : F) (n : Nat) :
    ((C half : Poly)^n).totalDegree ≤ 0 := by
  have hc : (C half : Poly).totalDegree ≤ 0 := by simp
  have hpow := totalDegree_pow (C half : Poly) n
  exact hpow.trans (by simpa using Nat.mul_le_mul_left n hc)

theorem sourceGather_degree (half : F) (w : Nat → Poly) (D : Nat)
    (hw : ∀ n, (w n).totalDegree ≤ D) (i : Nat) :
    (sourceGather (C half : Poly) w i).totalDegree ≤ D := by
  rw [sourceGather_powers]
  apply list_sum_degree_le
  intro e he
  have hmul := totalDegree_mul ((C half : Poly)^e.2) (w e.1)
  exact hmul.trans (by
    simpa using Nat.add_le_add (constant_pow_degree_le half e.2) (hw e.1))

lemma zeroExtend_degree_le (n : Nat) (w : Nat → Poly) (D : Nat)
    (hw : ∀ i, (w i).totalDegree ≤ D) (i : Nat) :
    (zeroExtend n w i).totalDegree ≤ D := by
  unfold zeroExtend
  split_ifs with h
  · exact hw i
  · simp

lemma interleave_degree_le (e o : Nat → Poly) (D : Nat)
    (he : ∀ i, (e i).totalDegree ≤ D) (ho : ∀ i, (o i).totalDegree ≤ D) (i : Nat) :
    (interleave e o i).totalDegree ≤ D := by
  unfold interleave
  split_ifs with h
  · exact he (i / 2)
  · exact ho (i / 2)

lemma chordDualEven_degree_le (half : Poly) (we wo : Nat → Poly)
    (a b c : Poly) (D E : Nat)
    (hwe : ∀ i, (we i).totalDegree ≤ D)
    (hwo : ∀ i, (wo i).totalDegree ≤ D)
    (ha : a.totalDegree ≤ E) (hb : b.totalDegree ≤ E) (hc : c.totalDegree ≤ E)
    (i : Nat) :
    (chordDualEven half we wo a b c i).totalDegree ≤ D + E := by
  unfold chordDualEven
  have hA : (a * we i).totalDegree ≤ D + E := by
    have hmul := totalDegree_mul a (we i)
    simpa [Nat.add_comm] using hmul.trans (Nat.add_le_add ha (hwe i))
  have hB : (b * sourceGather half we i).totalDegree ≤ D + E := by
    have hg := sourceGather_degree (half := half) (w := we) D hwe i
    have hmul := totalDegree_mul b (sourceGather half we i)
    simpa [Nat.add_comm] using hmul.trans (Nat.add_le_add hb hg)
  have hC : (c * wo i).totalDegree ≤ D + E := by
    have hmul := totalDegree_mul c (wo i)
    simpa [Nat.add_comm] using hmul.trans (Nat.add_le_add hc (hwo i))
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le hA hB)) hC)

lemma chordDualOdd_degree_le (half : Poly) (we wo : Nat → Poly)
    (a b c : Poly) (D E : Nat)
    (hwe : ∀ i, (we i).totalDegree ≤ D)
    (hwo : ∀ i, (wo i).totalDegree ≤ D)
    (hdouble : ∀ i, (sourceGather half (fun j => sourceGather half we j) i).totalDegree ≤ D)
    (hwoGather : ∀ i, (sourceGather half wo i).totalDegree ≤ D)
    (ha : a.totalDegree ≤ E) (hb : b.totalDegree ≤ E) (hc : c.totalDegree ≤ E)
    (i : Nat) :
    (chordDualOdd half we wo a b c i).totalDegree ≤ D + E := by
  unfold chordDualOdd
  have hsub : (we i - sourceGather half (fun j => sourceGather half we j) i).totalDegree ≤ D :=
    (totalDegree_sub _ _).trans (max_le (hwe i) (hdouble i))
  have hC : (c * (we i - sourceGather half (fun j => sourceGather half we j) i)).totalDegree ≤ D + E := by
    have hmul := totalDegree_mul c (we i - sourceGather half (fun j => sourceGather half we j) i)
    simpa [Nat.add_comm] using hmul.trans (Nat.add_le_add hc hsub)
  have hA : (a * wo i).totalDegree ≤ D + E := by
    have hmul := totalDegree_mul a (wo i)
    simpa [Nat.add_comm] using hmul.trans (Nat.add_le_add ha (hwo i))
  have hB : (b * sourceGather half wo i).totalDegree ≤ D + E := by
    have hmul := totalDegree_mul b (sourceGather half wo i)
    simpa [Nat.add_comm] using hmul.trans (Nat.add_le_add hb (hwoGather i))
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le hC hA)) hB)

theorem sourceChordTranspose_degree (half : F) (w : Nat → Poly)
    (a b c : Poly) (D E : Nat)
    (hw : ∀ n, (w n).totalDegree ≤ D)
    (ha : a.totalDegree ≤ E) (hb : b.totalDegree ≤ E) (hc : c.totalDegree ≤ E)
    (i : Nat) :
    (sourceChordTranspose (C half : Poly) w a b c i).totalDegree ≤ D + E := by
  unfold sourceChordTranspose
  apply interleave_degree_le
  · intro n
    apply chordDualEven_degree_le (C half : Poly)
    · exact zeroExtend_degree_le 512 (fun j => w (2*j)) D (fun j => hw (2*j)) n
    · exact zeroExtend_degree_le 512 (fun j => w (2*j+1)) D (fun j => hw (2*j+1)) n
    · exact ha
    · exact hb
    · exact hc
  · intro n
    have hwe : ∀ j, (zeroExtend 512 (fun j => w (2*j)) j).totalDegree ≤ D :=
      fun j => zeroExtend_degree_le 512 (fun k => w (2*k)) D (fun k => hw (2*k)) j
    have hwo : ∀ j, (zeroExtend 512 (fun j => w (2*j+1)) j).totalDegree ≤ D :=
      fun j => zeroExtend_degree_le 512 (fun k => w (2*k+1)) D (fun k => hw (2*k+1)) j
    apply chordDualOdd_degree_le (C half : Poly)
    · exact hwe
    · exact hwo
    · intro j
      exact sourceGather_degree (C half : Poly)
        (fun k => sourceGather (C half : Poly) (zeroExtend 512 (fun m => w (2*m))) k)
        D (fun k => sourceGather_degree (C half : Poly)
          (zeroExtend 512 (fun m => w (2*m))) D hwe k) j
    · intro j
      exact sourceGather_degree (C half : Poly)
        (zeroExtend 512 (fun k => w (2*k+1))) D hwo j
    · exact ha
    · exact hb
    · exact hc
    · exact n

#print axioms sourceGather_degree
#print axioms sourceChordTranspose_degree
end
end AspisV8R19.R838SourceWeightDegree
