import AspisR1ProducerChecked47.Funs
import AspisR1ProducerRelease47.Funs
import R1Z.ProverCommitWrapping47
/-! Checked-success transport into the independently extracted release
wrapping arithmetic. No canonical-input or callee-success law is assumed. -/
set_option autoImplicit false
namespace R1Z.ProverCommitRelease47
open Aeneas Aeneas.Std Result ProverCommitWrapping47

def convC (x : AspisR1ProducerChecked47.field.CM31) : AspisR1ProducerRelease47.field.CM31 := ⟨x.a,x.b⟩
def convQ (x : AspisR1ProducerChecked47.field.QM31) : AspisR1ProducerRelease47.field.QM31 := ⟨convC x.c0,convC x.c1⟩
def convE (x : AspisR1ProducerChecked47.field.wide_exact.WideExact) : AspisR1ProducerRelease47.field.wide_exact.WideExact :=
  ⟨convQ x.c0,convQ x.c1⟩

theorem mAdd (x y : U32) : Refines id (AspisR1ProducerChecked47.field.M31.add x y) (AspisR1ProducerRelease47.field.M31.add x y) := by
  unfold AspisR1ProducerChecked47.field.M31.add AspisR1ProducerRelease47.field.M31.add
  rw [AspisR1ProducerChecked47.field.P,AspisR1ProducerRelease47.field.P]
  refine ProverCommitWrapping47.bind id id _ _ _ _ (add x y) ?_
  intro s
  by_cases hs : s ≥ 2147483647#u32
  · simp only [id,hs,if_true]
    exact ProverCommitWrapping47.bind id id _ _ _ _ (sub s _) (fun t => pure id t)
  · simp only [id,hs,if_false]
    exact pure id s

theorem mSub (x y : U32) : Refines id (AspisR1ProducerChecked47.field.M31.sub x y) (AspisR1ProducerRelease47.field.M31.sub x y) := by
  unfold AspisR1ProducerChecked47.field.M31.sub AspisR1ProducerRelease47.field.M31.sub
  rw [AspisR1ProducerChecked47.field.P,AspisR1ProducerRelease47.field.P]
  refine ProverCommitWrapping47.bind id id _ _ _ _ (add x _) ?_
  intro s
  refine ProverCommitWrapping47.bind id id _ _ _ _ (sub s y) ?_
  intro t
  by_cases ht : t ≥ 2147483647#u32
  · simp only [id,ht,if_true]
    exact ProverCommitWrapping47.bind id id _ _ _ _ (sub t _) (fun r => pure id r)
  · simp only [id,ht,if_false]
    exact pure id t

theorem mDouble (x : U32) : Refines id (AspisR1ProducerChecked47.field.M31.double x) (AspisR1ProducerRelease47.field.M31.double x) :=
  mAdd x x

theorem shift31 (x : U64) : UScalar.shiftRight_UScalar x (31#u32) =
    ok (Std.U64.wrapping_shr x (31#u32)) := by rfl

theorem shift_ref (x : U64) : Refines id (UScalar.shiftRight_UScalar x (31#u32))
    (lift (Std.U64.wrapping_shr x (31#u32))) := by
  rw [shift31]
  exact refl _

theorem reduce (x : U64) : Refines id (AspisR1ProducerChecked47.field.reduce_u64 x) (AspisR1ProducerRelease47.field.reduce_u64 x) := by
  unfold AspisR1ProducerChecked47.field.reduce_u64 AspisR1ProducerRelease47.field.reduce_u64
  rw [AspisR1ProducerChecked47.field.P,AspisR1ProducerRelease47.field.P]
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro p0
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro lo0
  refine ProverCommitWrapping47.bind id id _ _ _ _ (shift_ref x) ?_
  intro hi0
  refine ProverCommitWrapping47.bind id id _ _ _ _ (add lo0 hi0) ?_
  intro x1
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro p1
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro lo1
  refine ProverCommitWrapping47.bind id id _ _ _ _ (shift_ref x1) ?_
  intro hi1
  refine ProverCommitWrapping47.bind id id _ _ _ _ (add lo1 hi1) ?_
  intro x2
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro x3
  by_cases hh : x3 ≥ 2147483647#u32
  · simp only [id,hh,if_true]
    exact sub _ _
  · simp only [id,hh,if_false]
    exact pure id _

theorem mReduce (x : U64) : Refines id (AspisR1ProducerChecked47.field.M31.reduce_u64 x) (AspisR1ProducerRelease47.field.M31.reduce_u64 x) := by
  unfold AspisR1ProducerChecked47.field.M31.reduce_u64 AspisR1ProducerRelease47.field.M31.reduce_u64
  exact ProverCommitWrapping47.bind id id _ _ _ _ (reduce x) (fun y => pure id y)

theorem mMul (x y : U32) : Refines id (AspisR1ProducerChecked47.field.M31.mul x y) (AspisR1ProducerRelease47.field.M31.mul x y) := by
  unfold AspisR1ProducerChecked47.field.M31.mul AspisR1ProducerRelease47.field.M31.mul
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro a
  refine ProverCommitWrapping47.bind id id _ _ _ _ (refl _) ?_
  intro b
  refine ProverCommitWrapping47.bind id id _ _ _ _ (mul a b) ?_
  intro s
  exact ProverCommitWrapping47.bind id id _ _ _ _ (reduce s) (fun y => pure id y)

theorem addC (x y : AspisR1ProducerChecked47.field.CM31) :
    Refines convC (AspisR1ProducerChecked47.field.CM31.add x y) (AspisR1ProducerRelease47.field.CM31.add (convC x) (convC y)) := by
  unfold AspisR1ProducerChecked47.field.CM31.add AspisR1ProducerRelease47.field.CM31.add
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mAdd _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mAdd _ _) ?_
  intro b
  exact pure convC ⟨a,b⟩

theorem subC (x y : AspisR1ProducerChecked47.field.CM31) :
    Refines convC (AspisR1ProducerChecked47.field.CM31.sub x y) (AspisR1ProducerRelease47.field.CM31.sub (convC x) (convC y)) := by
  unfold AspisR1ProducerChecked47.field.CM31.sub AspisR1ProducerRelease47.field.CM31.sub
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mSub _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mSub _ _) ?_
  intro b
  exact pure convC ⟨a,b⟩

theorem mulC (x y : AspisR1ProducerChecked47.field.CM31) :
    Refines convC (AspisR1ProducerChecked47.field.CM31.mul x y) (AspisR1ProducerRelease47.field.CM31.mul (convC x) (convC y)) := by
  unfold AspisR1ProducerChecked47.field.CM31.mul AspisR1ProducerRelease47.field.CM31.mul
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mMul _ _) ?_
  intro m0
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mMul _ _) ?_
  intro m1
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (refl _) ?_
  intro xa
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (refl _) ?_
  intro xb
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (add xa xb) ?_
  intro s0
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (refl _) ?_
  intro ya
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (refl _) ?_
  intro yb
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (add ya yb) ?_
  intro s1
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mul _ _) ?_
  intro p
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mReduce p) ?_
  intro m2
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mSub m0 m1) ?_
  intro a
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mSub m2 m0) ?_
  intro b
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mSub b m1) ?_
  intro c
  exact pure convC ⟨a,c⟩

theorem rC (x : AspisR1ProducerChecked47.field.CM31) :
    Refines convC (AspisR1ProducerChecked47.field.mul_by_r x) (AspisR1ProducerRelease47.field.mul_by_r (convC x)) := by
  unfold AspisR1ProducerChecked47.field.mul_by_r AspisR1ProducerRelease47.field.mul_by_r
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mDouble _) ?_
  intro a
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mSub _ _) ?_
  intro b
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mDouble _) ?_
  intro c
  refine ProverCommitWrapping47.bind id convC _ _ _ _ (mAdd _ _) ?_
  intro d
  exact pure convC ⟨b,d⟩

theorem addQ (x y : AspisR1ProducerChecked47.field.QM31) :
    Refines convQ (AspisR1ProducerChecked47.field.QM31.add x y) (AspisR1ProducerRelease47.field.QM31.add (convQ x) (convQ y)) := by
  unfold AspisR1ProducerChecked47.field.QM31.add AspisR1ProducerRelease47.field.QM31.add
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (addC _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (addC _ _) ?_
  intro b
  exact pure convQ ⟨a,b⟩

theorem subQ (x y : AspisR1ProducerChecked47.field.QM31) :
    Refines convQ (AspisR1ProducerChecked47.field.QM31.sub x y) (AspisR1ProducerRelease47.field.QM31.sub (convQ x) (convQ y)) := by
  unfold AspisR1ProducerChecked47.field.QM31.sub AspisR1ProducerRelease47.field.QM31.sub
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (subC _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (subC _ _) ?_
  intro b
  exact pure convQ ⟨a,b⟩

theorem mulQ (x y : AspisR1ProducerChecked47.field.QM31) :
    Refines convQ (AspisR1ProducerChecked47.field.QM31.mul x y) (AspisR1ProducerRelease47.field.QM31.mul (convQ x) (convQ y)) := by
  unfold AspisR1ProducerChecked47.field.QM31.mul AspisR1ProducerRelease47.field.QM31.mul
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (mulC _ _) ?_
  intro m0
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (mulC _ _) ?_
  intro m1
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (addC _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (addC _ _) ?_
  intro b
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (mulC _ _) ?_
  intro m2
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (rC _) ?_
  intro r
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (addC _ _) ?_
  intro c
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (subC _ _) ?_
  intro d
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (subC _ _) ?_
  intro e
  exact pure convQ ⟨c,e⟩

theorem mulU (x : AspisR1ProducerChecked47.field.QM31) :
    Refines convQ (AspisR1ProducerChecked47.field.wide_exact.mul_u x) (AspisR1ProducerRelease47.field.wide_exact.mul_u (convQ x)) := by
  unfold AspisR1ProducerChecked47.field.wide_exact.mul_u AspisR1ProducerRelease47.field.wide_exact.mul_u
  refine ProverCommitWrapping47.bind convC convQ _ _ _ _ (rC _) ?_
  intro c
  exact pure convQ ⟨c,x.c0⟩

theorem addE (x y : AspisR1ProducerChecked47.field.wide_exact.WideExact) :
    Refines convE (AspisR1ProducerChecked47.field.wide_exact.WideExact.add x y)
      (AspisR1ProducerRelease47.field.wide_exact.WideExact.add (convE x) (convE y)) := by
  unfold AspisR1ProducerChecked47.field.wide_exact.WideExact.add AspisR1ProducerRelease47.field.wide_exact.WideExact.add
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (addQ _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (addQ _ _) ?_
  intro b
  exact pure convE ⟨a,b⟩

theorem mulE (x y : AspisR1ProducerChecked47.field.wide_exact.WideExact) :
    Refines convE (AspisR1ProducerChecked47.field.wide_exact.WideExact.mul x y)
      (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (convE x) (convE y)) := by
  unfold AspisR1ProducerChecked47.field.wide_exact.WideExact.mul AspisR1ProducerRelease47.field.wide_exact.WideExact.mul
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (mulQ _ _) ?_
  intro ac
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (mulQ _ _) ?_
  intro bd
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (addQ _ _) ?_
  intro a
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (addQ _ _) ?_
  intro b
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (mulQ _ _) ?_
  intro cross
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (mulU _) ?_
  intro u
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (addQ _ _) ?_
  intro c0
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (subQ _ _) ?_
  intro diff
  refine ProverCommitWrapping47.bind convQ convE _ _ _ _ (subQ _ _) ?_
  intro c1
  exact pure convE ⟨c0,c1⟩

#print axioms mAdd
#print axioms mSub
#print axioms mDouble
#print axioms shift31
#print axioms shift_ref
#print axioms reduce
#print axioms mReduce
#print axioms mMul
#print axioms addC
#print axioms subC
#print axioms mulC
#print axioms rC
#print axioms addQ
#print axioms subQ
#print axioms mulQ
#print axioms mulU
#print axioms addE
#print axioms mulE
end R1Z.ProverCommitRelease47
