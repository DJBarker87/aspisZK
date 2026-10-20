import GeometryGroupingCallback
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryGrouping.Proof
open alloc.vec
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem grouping_callback_success (flat : Vec M31) (i j : Usize)
    (x : M31) (capture : geometry_groups.closure.closure)
    (hb : 5*i.val+j.val < flat.val.length)
    (h : geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (flat,i) j = .ok (x,capture)) :
    capture=(flat,i) ∧ x=flat.val.getD (5*i.val+j.val) 0#u32 := by
  unfold geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut at h
  rcases bind_ok_inv h with ⟨prod,hprod,h⟩
  rcases bind_ok_inv h with ⟨idx,hidx,h⟩
  rcases bind_ok_inv h with ⟨v,hread,h⟩
  have he : (v,(flat,i))=(x,capture) := Result.ok.inj h
  cases he
  have hm := UScalar.mul_equiv 5#usize i
  change UScalar.mul (5#usize) i = .ok prod at hprod
  rw [hprod] at hm
  have hp : prod.val=5*i.val := by simpa only [show (5#usize).val=5 from rfl] using hm.2.1
  have ha := UScalar.add_equiv prod j
  rw [hidx] at ha
  have hi : idx.val=5*i.val+j.val := by simpa only [hp] using ha.2.1
  have hbound : idx.val<flat.val.length := by omega
  rw [Vec.index_slice_index] at hread
  obtain ⟨v,hv,hvalue⟩ := WP.spec_imp_exists (Vec.index_usize_spec flat idx hbound)
  have he : v=x := Result.ok.inj (hv.symm.trans hread)
  rw [he] at hvalue
  refine ⟨rfl,?_⟩
  rw [List.getD_eq_getElem flat.val 0#u32 hb]
  simpa only [hi] using hvalue

#print axioms grouping_callback_success
end AspisR1GeometryGrouping.Proof
