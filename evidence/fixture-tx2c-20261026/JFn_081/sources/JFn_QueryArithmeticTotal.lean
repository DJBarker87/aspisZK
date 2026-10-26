import SAQ_Decoder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_QueryArithmeticTotal
open Aeneas Aeneas.Std Result SAQ_WideABI

/-- Transport the existing source QM31 totality across its nominal record. -/
theorem qmTotal (x y : Q)
    (hx : AspisR1CurrentWide.Proof.CanonicalQM x) (hy : AspisR1CurrentWide.Proof.CanonicalQM y) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul x y=ok z ∧ AspisR1CurrentWide.Proof.CanonicalQM z := by
  obtain ⟨out,ho,_,_⟩ := ExtractedCurrentQM31Exact.current_qm_mul_exact
    (AspisR1CurrentWide.Proof.toQM x) (AspisR1CurrentWide.Proof.toQM y) hx hy
  have hm := AspisR1CurrentWide.Proof.qm_mul_same x y
  cases hr : AspisR1CurrentWide.field.QM31.mul x y with
  | fail e => simp only [hr,bind_tc_fail] at hm;rw [ho] at hm;cases hm
  | div => simp only [hr,bind_tc_div] at hm;rw [ho] at hm;cases hm
  | ok z => exact ⟨z,rfl,(AspisR1CurrentWide.Proof.qm_mul_success x y z hx hy hr).1⟩
#print axioms qmTotal

theorem add (x y : E) (hx : Port4C_QueryArithmetic.CanonE x) (hy : Port4C_QueryArithmetic.CanonE y) :
    ∃ z, SAQ_Arithmetic.add x y=ok z ∧ Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨z,call,canon,_⟩ := AspisR1CurrentWide.Proof.wide_add_total_exact (toW x) (toW y)
    ((w_canonical x).mp hx) ((w_canonical y).mp hy)
  refine ⟨fromW z,?_,(w_canonical (fromW z)).mpr canon⟩
  simp only [SAQ_Arithmetic.add,call,bind_tc_ok]

theorem mulK (x y : K) (hx : Port3_FlushInstall.Canonical x) (hy : Port3_FlushInstall.Canonical y) :
    ∃ z, SAQ_Arithmetic.mulK x y=ok z ∧ Port3_FlushInstall.Canonical z := by
  obtain ⟨z,call,canon⟩ := qmTotal (toQ x) (toQ y)
    ((q_canonical x).mp hx) ((q_canonical y).mp hy)
  refine ⟨fromQ z,?_,(q_canonical (fromQ z)).mpr canon⟩
  simp only [SAQ_Arithmetic.mulK,call,bind_tc_ok]

theorem mulE (x : E) (q : K) (hx : Port4C_QueryArithmetic.CanonE x)
    (hq : Port3_FlushInstall.Canonical q) :
    ∃ z, SAQ_MixedSource.mulE x q=ok z ∧ Port4C_QueryArithmetic.CanonE z := by
  have cq := (q_canonical q).mp hq
  obtain ⟨a,ha,ca⟩ := qmTotal (toW x).c0 (toQ q)
    ((w_canonical x).mp hx).1 cq
  obtain ⟨b,hb,cb⟩ := qmTotal (toW x).c1 (toQ q)
    ((w_canonical x).mp hx).2 cq
  let z : W := ⟨a,b⟩
  refine ⟨fromW z,?_,(w_canonical (fromW z)).mpr ⟨ca,cb⟩⟩
  simp only [SAQ_MixedSource.mulE,SAQ_MixedSource.source,SAQ_MixedSource.canonical_same _ cq,
    ha,hb,bind_tc_ok,z]

#print axioms add
#print axioms mulK
#print axioms mulE
end AspisR1.JFn_QueryArithmeticTotal
end
