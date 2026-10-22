import CurrentWideMulSourceGraph
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev ExactM := AspisV8R15.ExactTowerBase.M31Exact
abbrev ExactC := AspisV8R15.ExactTowerBase.CM31Exact
def decodeM (x : U32) : ExactM := x.val
def decodeC (x : field.CM31) : ExactC := ⟨decodeM x.a,decodeM x.b⟩
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem m31_add_exact (x y z : U32) (h : field.M31.add x y = .ok z) :
    decodeM z = decodeM x + decodeM y := by
  rw [m31_add_same] at h
  exact R17CurrentM31Semantics.current_add_decode x y z h

theorem m31_sub_exact (x y z : U32) (h : field.M31.sub x y = .ok z) :
    decodeM z = decodeM x - decodeM y := by
  rw [m31_sub_same] at h
  exact R17CurrentM31Semantics.current_sub_decode x y z h

theorem cm_sub_exact (x y z : field.CM31) (h : field.CM31.sub x y = .ok z) :
    decodeC z = decodeC x - decodeC y := by
  unfold field.CM31.sub at h
  rcases bind_ok_inv h with ⟨a,ha,h⟩
  rcases bind_ok_inv h with ⟨b,hb,h⟩
  have he : ({a:=a,b:=b} : field.CM31) = z := Result.ok.inj h
  subst z
  apply QuadraticAlgebra.ext
  · exact m31_sub_exact x.a y.a a ha
  · exact m31_sub_exact x.b y.b b hb

theorem qm_sub_exact (x y z : field.QM31) (h : field.QM31.sub x y = .ok z) :
    decodeQM z = decodeQM x - decodeQM y := by
  unfold field.QM31.sub at h
  rcases bind_ok_inv h with ⟨a,ha,h⟩
  rcases bind_ok_inv h with ⟨b,hb,h⟩
  have he : ({c0:=a,c1:=b} : field.QM31) = z := Result.ok.inj h
  subst z
  apply QuadraticAlgebra.ext
  · exact cm_sub_exact x.c0 y.c0 a ha
  · exact cm_sub_exact x.c1 y.c1 b hb

theorem mul_by_r_exact (x z : field.CM31) (h : field.mul_by_r x = .ok z) :
    decodeC z = AspisV8R15.ExactTowerBase.qm31R * decodeC x := by
  unfold field.mul_by_r field.M31.double at h
  rcases bind_ok_inv h with ⟨a2,ha2,h⟩
  rcases bind_ok_inv h with ⟨lo,hlo,h⟩
  rcases bind_ok_inv h with ⟨b2,hb2,h⟩
  rcases bind_ok_inv h with ⟨hi,hhi,h⟩
  have he : ({a:=lo,b:=hi} : field.CM31) = z := Result.ok.inj h
  subst z
  have ha2v := m31_add_exact x.a x.a a2 ha2
  have hlov := m31_sub_exact a2 x.b lo hlo
  have hb2v := m31_add_exact x.b x.b b2 hb2
  have hhiv := m31_add_exact x.a b2 hi hhi
  apply QuadraticAlgebra.ext
  · simp only [decodeC, AspisV8R15.ExactTowerBase.qm31R,
      QuadraticAlgebra.re_mul]
    rw [hlov,ha2v]
    ring
  · simp only [decodeC, AspisV8R15.ExactTowerBase.qm31R,
      QuadraticAlgebra.im_mul]
    rw [hhiv,hb2v]
    ring

theorem mul_u_exact (x z : field.QM31) (h : field.wide_exact.mul_u x = .ok z) :
    decodeQM z = AspisWideTower.wideU * decodeQM x := by
  unfold field.wide_exact.mul_u at h
  rcases bind_ok_inv h with ⟨r,hr,h⟩
  have he : ({c0:=r,c1:=x.c0} : field.QM31) = z := Result.ok.inj h
  subst z
  have hd := mul_by_r_exact x.c1 r hr
  apply QuadraticAlgebra.ext
  · simpa [decodeQM,AspisR1.ExtractedCurrentQM31Exact.decode,toQM,toCM,
      decodeC,decodeM,AspisWideTower.wideU,mul_comm] using hd
  · simp [decodeQM,AspisR1.ExtractedCurrentQM31Exact.decode,toQM,toCM,
      AspisWideTower.wideU]

#print axioms m31_add_exact
#print axioms m31_sub_exact
#print axioms cm_sub_exact
#print axioms qm_sub_exact
#print axioms mul_by_r_exact
#print axioms mul_u_exact
end AspisR1CurrentWide.Proof
