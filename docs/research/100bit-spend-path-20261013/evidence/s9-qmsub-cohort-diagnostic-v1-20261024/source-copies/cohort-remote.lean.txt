import CurrentWideQMField
import ExtractedCurrentTowerAdd
import AspisV8R17.QM31WordTower
import AspisV8R15.ExactTowerBase
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
private abbrev OldQM := AspisR1Qm31ArithmeticProbe.field.QM31
private abbrev OldCM := AspisR1Qm31ArithmeticProbe.field.CM31
private abbrev Words := AspisR1.ExtractedCurrentQM31Mul.wordsQM
theorem qm_sub_success (x y z : field.QM31)
    (hx : CanonicalQM x) (hy : CanonicalQM y)
    (h : field.QM31.sub x y = .ok z) :
    CanonicalQM z ∧ decodeQM z = decodeQM x - decodeQM y := by
  let ox := toQM x
  let oy := toQM y
  obtain ⟨a, ha, hca, hva, hvb⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod ox.c0 oy.c0
      (by simpa [CanonicalQM, ox] using hx.1)
      (by simpa [CanonicalQM, oy] using hy.1)
  obtain ⟨b, hb, hcb, hvc, hvd⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod ox.c1 oy.c1
      (by simpa [CanonicalQM, ox] using hx.2)
      (by simpa [CanonicalQM, oy] using hy.2)
  let out : field.QM31 := ⟨⟨a.a, a.b⟩, ⟨b.a, b.b⟩⟩
  have h0map := cm_sub_same x.c0 y.c0
  have ha' : AspisR1Qm31ArithmeticProbe.field.CM31.sub (toCM x.c0) (toCM y.c0) = .ok a := by simpa [ox, oy, toQM, toCM] using ha
  rw [ha'] at h0map
  have h1map := cm_sub_same x.c1 y.c1
  have hb' : AspisR1Qm31ArithmeticProbe.field.CM31.sub (toCM x.c1) (toCM y.c1) = .ok b := by simpa [ox, oy, toQM, toCM] using hb
  rw [hb'] at h1map
  have h0 : field.CM31.sub x.c0 y.c0 = .ok out.c0 := by
    cases hh : field.CM31.sub x.c0 y.c0 with
    | fail e => simp [hh] at h0map
    | div => simp [hh] at h0map
    | ok v =>
      have hv : toCM v = a := by simpa [hh] using h0map
      have hv' : v = out.c0 := by cases v; cases a; cases hv; rfl
      rw [hv']
  have h1 : field.CM31.sub x.c1 y.c1 = .ok out.c1 := by
    cases hh : field.CM31.sub x.c1 y.c1 with
    | fail e => simp [hh] at h1map
    | div => simp [hh] at h1map
    | ok v =>
      have hv : toCM v = b := by simpa [hh] using h1map
      have hv' : v = out.c1 := by cases v; cases b; cases hv; rfl
      rw [hv']
  have hout : field.QM31.sub x y = .ok out := by
    simp [field.QM31.sub, h0, h1]
  have he : z = out := Result.ok.inj (h.symm.trans hout)
  constructor
  · rw [he]
    change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM (toQM out)
    simpa [toQM, toCM, out, AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM] using
      (show AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
        (⟨a,b⟩ : OldQM) from ⟨hca,hcb⟩)
  · rw [he]
    change AspisV8R17.QM31WordTower.decodeQ (Words (toQM out)) =
      AspisV8R17.QM31WordTower.decodeQ (Words ox) -
      AspisV8R17.QM31WordTower.decodeQ (Words oy)
    have hword : Words (toQM out) =
        AspisV8R17.GeneratedQM31Linear.qmSubWords (Words ox) (Words oy) := by
      simp only [Words, AspisR1.ExtractedCurrentQM31Mul.wordsQM,
        AspisR1.ExtractedCurrentQM31Mul.subWords]
      exact Prod.ext (Prod.ext hva hvb) (Prod.ext hvc hvd)
    rw [hword]
    have hyWords : AspisV8R17.QM31WordResidues.CanonicalPair (Words oy).1 ∧
        AspisV8R17.QM31WordResidues.CanonicalPair (Words oy).2 := by
      change (oy.c0.a.val < AspisV8R17.RawReducer.P ∧ oy.c0.b.val < AspisV8R17.RawReducer.P) ∧
        (oy.c1.a.val < AspisV8R17.RawReducer.P ∧ oy.c1.b.val < AspisV8R17.RawReducer.P)
      exact hy
    exact AspisV8R17.QM31WordTower.decode_sub _ _ hyWords


end AspisR1CurrentWide.Proof
