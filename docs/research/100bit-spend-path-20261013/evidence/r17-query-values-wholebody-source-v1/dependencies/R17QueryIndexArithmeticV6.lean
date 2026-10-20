import Aeneas
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace R17QueryIndexArithmeticV1

def checkedLineIndices (u : Usize) : Result (Usize × Usize) := do
  let qx ← UScalar.div u (4#usize)
  let ix ← UScalar.mul qx (4#usize)
  let qy ← UScalar.div u (4#usize)
  let base ← UScalar.mul qy (4#usize)
  let iy ← UScalar.add base (3#usize)
  pure (ix, iy)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem successful_mul_val {a b c : Usize}
    (h : UScalar.mul a b = .ok c) : c.val = a.val * b.val := by
  have he := UScalar.mul_equiv a b
  rw [h] at he
  exact he.2.1

private theorem successful_add_val {a b c : Usize}
    (h : UScalar.add a b = .ok c) : c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  have h' : (a + b : Result Usize) = .ok c := by
    change (a + b : Result Usize) = .ok c at h
    exact h
  rw [h'] at he
  exact he.2.1

theorem successful_checkedLineIndices
    (u ix iy : Usize) (hu : u.val < 262144)
    (h : checkedLineIndices u = .ok (ix, iy)) :
    ix.val = (u.val / 4) * 4 ∧
    iy.val = (u.val / 4) * 4 + 3 ∧
    ix.val < 262144 ∧ iy.val < 262144 := by
  unfold checkedLineIndices at h
  rcases bind_ok_inv h with ⟨qx, hqx, hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨ix0, hix, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨qy, hqy, hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨base, hby, hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨iy0, hiy, hrest5⟩
  have hpair : (ix0, iy0) = (ix, iy) := Result.ok.inj hrest5
  rcases hpair with ⟨rfl, rfl⟩
  have hqxVal : qx.val = u.val / 4 := by
    obtain ⟨q, hq, hv⟩ := UScalar.div_spec u (y := 4#usize) (by decide)
    change (u / (4#usize) : Result Usize) = .ok qx at hqx
    have heq : q = qx := Result.ok.inj (hq.symm.trans hqx)
    rw [heq] at hv
    simpa only [UScalar.ofNatCore_val_eq] using hv
  have hqyVal : qy.val = u.val / 4 := by
    obtain ⟨q, hq, hv⟩ := UScalar.div_spec u (y := 4#usize) (by decide)
    change (u / (4#usize) : Result Usize) = .ok qy at hqy
    have heq : q = qy := Result.ok.inj (hq.symm.trans hqy)
    rw [heq] at hv
    simpa only [UScalar.ofNatCore_val_eq] using hv
  have hixVal : ix.val = qx.val * 4 := by
    have hv := successful_mul_val hix
    simpa only [UScalar.ofNatCore_val_eq] using hv
  have hbyVal : base.val = qy.val * 4 := by
    have hv := successful_mul_val hby
    simpa only [UScalar.ofNatCore_val_eq] using hv
  have hiyVal : iy.val = base.val + 3 := by
    have hv := successful_add_val hiy
    simpa only [UScalar.ofNatCore_val_eq] using hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hixVal, hqxVal]
  · rw [hiyVal, hbyVal, hqyVal]
  · rw [hixVal, hqxVal]
    omega
  · rw [hiyVal, hbyVal, hqyVal]
    omega

#print axioms successful_checkedLineIndices
end R17QueryIndexArithmeticV1
