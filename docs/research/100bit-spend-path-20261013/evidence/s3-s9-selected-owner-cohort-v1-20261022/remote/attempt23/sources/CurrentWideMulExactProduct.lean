import CurrentWideMulExact
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

theorem mul_u_success_canonical (x z : field.QM31) (hx : CanonicalQM x)
    (h : field.wide_exact.mul_u x = .ok z) : CanonicalQM z := by
  obtain ⟨out,ho,hc⟩ := AspisR1CurrentWideMul.mul_u_total (toQM x) hx
  have hm := mul_u_same_minimal x
  rw [h,bind_tc_ok] at hm
  have he : toQM z = out := Result.ok.inj (hm.trans ho)
  change AspisR1CurrentWideMul.CanonicalQM (toQM z)
  rw [he]
  exact hc

theorem wide_mul_success_exact (x y z : E) (hx : CanonicalWide x) (hy : CanonicalWide y)
    (h : field.wide_exact.WideExact.mul x y = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x * decodeWide y := by
  have whole := h
  unfold field.wide_exact.WideExact.mul at h
  rcases bind_ok_inv h with ⟨ac,hac,h⟩
  rcases bind_ok_inv h with ⟨bd,hbd,h⟩
  rcases bind_ok_inv h with ⟨qa,hqa,h⟩
  rcases bind_ok_inv h with ⟨qb,hqb,h⟩
  rcases bind_ok_inv h with ⟨cross,hcross,h⟩
  rcases bind_ok_inv h with ⟨u,hu,h⟩
  rcases bind_ok_inv h with ⟨lo,hlo,h⟩
  rcases bind_ok_inv h with ⟨diff,hdiff,h⟩
  rcases bind_ok_inv h with ⟨hi,hhi,h⟩
  have he : ({c0:=lo,c1:=hi} : E) = z := Result.ok.inj h
  subst z
  have dac := qm_mul_success x.c0 y.c0 ac hx.1 hy.1 hac
  have dbd := qm_mul_success x.c1 y.c1 bd hx.2 hy.2 hbd
  have dqa := qm_add_success x.c0 x.c1 qa hx.1 hx.2 hqa
  have dqb := qm_add_success y.c0 y.c1 qb hy.1 hy.2 hqb
  have dcross := qm_mul_success qa qb cross dqa.1 dqb.1 hcross
  have cu := mul_u_success_canonical bd u dbd.1 hu
  have dlo := qm_add_success ac u lo dac.1 cu hlo
  refine ⟨wide_mul_source_success_canonical x y _ hx hy whole, ?_⟩
  apply QuadraticAlgebra.ext
  · simp only [decodeWide,QuadraticAlgebra.re_mul]
    rw [dlo.2,mul_u_exact bd u hu,dac.2,dbd.2]
    ring
  · simp only [decodeWide,QuadraticAlgebra.im_mul,zero_mul,zero_add,add_zero]
    rw [qm_sub_exact diff bd hi hhi,qm_sub_exact cross ac diff hdiff,
      dcross.2,dqa.2,dqb.2,dac.2,dbd.2]
    ring

theorem wide_mul_total_exact (x y : E) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, field.wide_exact.WideExact.mul x y = .ok z ∧
      CanonicalWide z ∧ decodeWide z = decodeWide x * decodeWide y := by
  obtain ⟨z,hz,hc⟩ := wide_mul_source_total_canonical x y hx hy
  exact ⟨z,hz,hc,(wide_mul_success_exact x y z hx hy hz).2⟩

#print axioms mul_u_success_canonical
#print axioms wide_mul_success_exact
#print axioms wide_mul_total_exact
end AspisR1CurrentWide.Proof
