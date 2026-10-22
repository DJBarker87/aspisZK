import CurrentWideField
import R17CurrentDomainCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev ExactCM := AspisV8R15.ExactTowerBase.CM31Exact
def decodeCM (x : field.CM31) : ExactCM :=
  ⟨R17CurrentM31Semantics.decode x.a,R17CurrentM31Semantics.decode x.b⟩
def CanonicalCM (x : field.CM31) : Prop :=
  AspisR1.ExtractedCurrentTowerAdd.CanonicalCM (toCM x)
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem mul_by_r_success (x z : field.CM31) (hx : CanonicalCM x)
    (h : field.mul_by_r x = .ok z) :
    CanonicalCM z ∧ decodeCM z = AspisV8R15.ExactTowerBase.qm31R * decodeCM x := by
  unfold field.mul_by_r at h
  rcases bind_ok_inv h with ⟨aa,haa,h⟩
  rcases bind_ok_inv h with ⟨a,ha,h⟩
  rcases bind_ok_inv h with ⟨bb,hbb,h⟩
  rcases bind_ok_inv h with ⟨b,hb,h⟩
  have he : ({a:=a,b:=b}:field.CM31)=z := Result.ok.inj h
  subst z
  rw [m31_double_same] at haa hbb
  rw [m31_sub_same] at ha
  rw [m31_add_same] at hb
  have hac := R17CurrentDomainCanonical.double_success_canonical x.a aa hx.1 haa
  have hbc := R17CurrentDomainCanonical.double_success_canonical x.b bb hx.2 hbb
  have halow := R17CurrentDomainCanonical.sub_success_canonical aa x.b a hac hx.2 ha
  obtain ⟨out,ho,_,hoc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x.a bb hx.1 hbc
  have hout : out=b := Result.ok.inj (ho.symm.trans hb)
  have hhigh : b.val<2147483647 := by simpa only [hout] using hoc
  have hdaa := R17CurrentM31Semantics.current_add_decode x.a x.a aa haa
  have hdbb := R17CurrentM31Semantics.current_add_decode x.b x.b bb hbb
  have hda := R17CurrentM31Semantics.current_sub_decode aa x.b a ha
  have hdb := R17CurrentM31Semantics.current_add_decode x.a bb b hb
  refine ⟨⟨halow,hhigh⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change R17CurrentM31Semantics.decode a =
      2*R17CurrentM31Semantics.decode x.a + (-1)*1*R17CurrentM31Semantics.decode x.b
    rw [hda,hdaa]
    ring
  · change R17CurrentM31Semantics.decode b =
      2*R17CurrentM31Semantics.decode x.b + 1*R17CurrentM31Semantics.decode x.a +
        0*1*R17CurrentM31Semantics.decode x.b
    rw [hdb,hdbb]
    ring

theorem mul_u_success (x z : field.QM31) (hx : CanonicalQM x)
    (h : field.wide_exact.mul_u x = .ok z) :
    CanonicalQM z ∧ decodeQM z = AspisWideTower.wideU * decodeQM x := by
  unfold field.wide_exact.mul_u at h
  rcases bind_ok_inv h with ⟨c,hc,h⟩
  have he : ({c0:=c,c1:=x.c0}:field.QM31)=z := Result.ok.inj h
  subst z
  have hr := mul_by_r_success x.c1 c hx.2 hc
  refine ⟨⟨hr.1,hx.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeCM c = 0 * decodeCM x.c0 + AspisV8R15.ExactTowerBase.qm31R * 1 * decodeCM x.c1
    rw [hr.2]
    ring
  · change decodeCM x.c0 = 0 * decodeCM x.c1 + 1 * decodeCM x.c0 + 0*1*decodeCM x.c1
    ring

#print axioms mul_by_r_success
#print axioms mul_u_success
end AspisR1CurrentWide.Proof
