import CurrentWideQMField
import AspisV8R17.QM31WordTower
import AspisV8R15.ExactTowerBase
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
private abbrev OldQM := AspisR1Qm31ArithmeticProbe.field.QM31
private abbrev OldCM := AspisR1Qm31ArithmeticProbe.field.CM31
private abbrev OldM31 := AspisR1Qm31ArithmeticProbe.field.M31
private abbrev Exact := AspisR1.ExtractedCurrentQM31Exact.QM31Exact
private abbrev MExact := AspisR1.ExtractedCurrentQM31Exact.M31Exact
private abbrev Words := AspisR1.ExtractedCurrentQM31Mul.wordsQM
private def scalarEmbedding (s : field.M31) : Exact :=
  ⟨⟨(s.val : MExact), (0 : MExact)⟩,
    ⟨(0 : MExact), (0 : MExact)⟩⟩

theorem qm_mul_m31_success (x : field.QM31) (s : field.M31) (z : field.QM31)
    (h : field.QM31.mul_m31 x s = .ok z) :
    CanonicalQM z ∧ decodeQM z = decodeQM x * scalarEmbedding s := by
  let old := toQM x
  obtain ⟨a, ha, hva, hca⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c0.a s
  obtain ⟨b, hb, hvb, hcb⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c0.b s
  obtain ⟨c, hc, hvc, hcc⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c1.a s
  obtain ⟨d, hd, hvd, hcd⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c1.b s
  let out : field.QM31 := ⟨⟨a,b⟩,⟨c,d⟩⟩
  have haNew : field.M31.mul x.c0.a s = .ok a := by rw [m31_mul_same]; exact ha
  have hbNew : field.M31.mul x.c0.b s = .ok b := by rw [m31_mul_same]; exact hb
  have hcNew : field.M31.mul x.c1.a s = .ok c := by rw [m31_mul_same]; exact hc
  have hdNew : field.M31.mul x.c1.b s = .ok d := by rw [m31_mul_same]; exact hd
  have hout : field.QM31.mul_m31 x s = .ok out := by
    simp [field.QM31.mul_m31, field.CM31.mul_m31, haNew, hbNew, hcNew, hdNew]
    rfl
  have he : z = out := Result.ok.inj (h.symm.trans hout)
  constructor
  · rw [he]
    change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM (toQM out)
    have hcan : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
        (⟨⟨a,b⟩,⟨c,d⟩⟩ : OldQM) := ⟨⟨hca,hcb⟩,⟨hcc,hcd⟩⟩
    simpa [toQM, toCM, out, OldQM] using hcan
  · rw [he]
    ext <;> simp [decodeQM, AspisR1.ExtractedCurrentQM31Exact.decode,
      AspisR1.ExtractedCurrentQM31Exact.M31Exact, scalarEmbedding, out, toQM, toCM,
      old, toQM, toCM, hva, hvb, hvc, hvd]

#print axioms qm_mul_m31_success
end AspisR1CurrentWide.Proof
