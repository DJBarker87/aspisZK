import CurrentWideMulU
import CurrentWideQMSubV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem wide_sub_success (x y z : E) (hx : CanonicalWide x) (hy : CanonicalWide y)
    (h : field.wide_exact.WideExact.sub x y = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x - decodeWide y := by
  unfold field.wide_exact.WideExact.sub at h
  rcases bind_ok_inv h with ⟨q0,h0,h⟩
  rcases bind_ok_inv h with ⟨q1,h1,h⟩
  have he : ({c0:=q0,c1:=q1} : E)=z := Result.ok.inj h
  subst z
  have hc0 := qm_sub_success x.c0 y.c0 q0 hx.1 hy.1 h0
  have hc1 := qm_sub_success x.c1 y.c1 q1 hx.2 hy.2 h1
  refine ⟨⟨hc0.1,hc1.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · exact hc0.2
  · exact hc1.2

theorem wide_mul_success (x y z : E) (hx : CanonicalWide x) (hy : CanonicalWide y)
    (h : field.wide_exact.WideExact.mul x y = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x * decodeWide y := by
  unfold field.wide_exact.WideExact.mul at h
  rcases bind_ok_inv h with ⟨ac,hac,h⟩
  rcases bind_ok_inv h with ⟨bd,hbd,h⟩
  rcases bind_ok_inv h with ⟨q0,h0,h⟩
  rcases bind_ok_inv h with ⟨q1,h1,h⟩
  rcases bind_ok_inv h with ⟨cross,hcross,h⟩
  rcases bind_ok_inv h with ⟨ubd,hubd,h⟩
  rcases bind_ok_inv h with ⟨low,hlow,h⟩
  rcases bind_ok_inv h with ⟨high0,hhigh0,h⟩
  rcases bind_ok_inv h with ⟨high,hhigh,h⟩
  have he : ({c0:=low,c1:=high} : E)=z := Result.ok.inj h
  subst z
  have cac := qm_mul_success x.c0 y.c0 ac hx.1 hy.1 hac
  have cbd := qm_mul_success x.c1 y.c1 bd hx.2 hy.2 hbd
  have c0 := qm_add_success x.c0 x.c1 q0 hx.1 hx.2 h0
  have c1 := qm_add_success y.c0 y.c1 q1 hy.1 hy.2 h1
  have cc := qm_mul_success q0 q1 cross c0.1 c1.1 hcross
  have cu := mul_u_success bd ubd cbd.1 hubd
  have cl := qm_add_success ac ubd low cac.1 cu.1 hlow
  have ch0 := qm_sub_success cross ac high0 cc.1 cac.1 hhigh0
  have ch := qm_sub_success high0 bd high ch0.1 cbd.1 hhigh
  refine ⟨⟨cl.1,ch.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeQM low = decodeQM x.c0*decodeQM y.c0 + AspisWideTower.wideU*decodeQM x.c1*decodeQM y.c1
    rw [cl.2,cac.2,cu.2,cbd.2]
    ring
  · change decodeQM high = decodeQM x.c0*decodeQM y.c1 + decodeQM x.c1*decodeQM y.c0 + 0*decodeQM x.c1*decodeQM y.c1
    rw [ch.2,ch0.2,cc.2,c0.2,c1.2,cac.2,cbd.2]
    ring

#print axioms wide_sub_success
#print axioms wide_mul_success
end AspisR1CurrentWide.Proof
