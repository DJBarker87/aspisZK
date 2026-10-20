import GeometryInputVecFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1GeometryInputs.Proof
open alloc.vec
abbrev QueryValues := U32 → Result (core.result.Result ((Array M31 5#usize) × M31) GeometryInputsError)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem body_done_none (qv : QueryValues) (queries : Array U32 22#usize)
    (end1 i : Usize) (zs flat zs1 flat1 : Vec M31)
    (h : geometry_inputs_indexed_loop.body qv queries end1 zs flat i = .ok (.done (zs1,flat1,none))) :
    end1.val ≤ i.val ∧ zs1 = zs ∧ flat1 = flat := by
  unfold geometry_inputs_indexed_loop.body at h
  by_cases hi : i < end1
  · simp only [hi,ite_true] at h
    rcases bind_ok_inv h with ⟨q,_,h⟩
    rcases bind_ok_inv h with ⟨r,_,h⟩
    cases r with
    | Ok val =>
      rcases val with ⟨values,z⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      rcases bind_ok_inv h with ⟨s,_,h⟩
      rcases bind_ok_inv h with ⟨f,_,h⟩
      rcases bind_ok_inv h with ⟨z,_,h⟩
      rcases bind_ok_inv h with ⟨j,_,h⟩
      cases h
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  · simp only [hi,ite_false] at h
    have he := ControlFlow.done.inj (Result.ok.inj h)
    cases he
    exact ⟨Nat.le_of_not_lt hi,rfl,rfl⟩

theorem body_no_done_ok (qv : QueryValues) (queries : Array U32 22#usize)
    (end1 i : Usize) (zs flat zs1 flat1 f z : Vec M31)
    (h : geometry_inputs_indexed_loop.body qv queries end1 zs flat i =
      .ok (.done (zs1,flat1,some (.Ok (f,z))))) : False := by
  unfold geometry_inputs_indexed_loop.body at h
  split at h
  · rcases bind_ok_inv h with ⟨q,_,h⟩
    rcases bind_ok_inv h with ⟨r,_,h⟩
    cases r with
    | Ok val =>
      rcases val with ⟨values,z⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      rcases bind_ok_inv h with ⟨s,_,h⟩
      rcases bind_ok_inv h with ⟨f,_,h⟩
      rcases bind_ok_inv h with ⟨z,_,h⟩
      rcases bind_ok_inv h with ⟨j,_,h⟩
      cases h
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  · cases h

theorem body_cont (qv : QueryValues) (queries : Array U32 22#usize)
    (end1 i j : Usize) (zs flat zs1 flat1 : Vec M31)
    (hend : end1.val ≤ 22)
    (h : geometry_inputs_indexed_loop.body qv queries end1 zs flat i = .ok (.cont (zs1,flat1,j))) :
    ∃ (hi : i.val < 22) (values : Array M31 5#usize) (z : M31),
      i.val < end1.val ∧ qv (queries.val.getD i.val 0#u32) = .ok (.Ok (values,z)) ∧
      flat1.val = flat.val ++ values.val ∧ zs1.val = zs.val ++ [z] ∧ j.val = i.val + 1 := by
  unfold geometry_inputs_indexed_loop.body at h
  by_cases hi : i < end1
  · simp only [hi,ite_true] at h
    rcases bind_ok_inv h with ⟨q,hq,h⟩
    rcases bind_ok_inv h with ⟨r,hr,h⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok val =>
      rcases val with ⟨values,z⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      rcases bind_ok_inv h with ⟨s,hs,h⟩
      rcases bind_ok_inv h with ⟨f,hf,h⟩
      rcases bind_ok_inv h with ⟨z1,hz,h⟩
      rcases bind_ok_inv h with ⟨j1,hj,h⟩
      have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      have hiN : i.val < end1.val := hi
      have hi22 : i.val < 22 := by omega
      have hiLen : i.val < queries.val.length := by rw [queries.property]; exact hi22
      obtain ⟨qr,hqr,hval⟩ := WP.spec_imp_exists (Array.index_usize_spec queries i hiLen)
      have heq : qr = q := Result.ok.inj (hqr.symm.trans hq)
      have hqval : q = queries.val[i.val] := by simpa only [heq] using hval
      have hsval : s.val = values.val := by
        have heq : s = Array.to_slice values := (Result.ok.inj hs).symm
        subst s
        rfl
      refine ⟨hi22,values,z,hi,?_,?_,push_success zs zs1 z hz,?_⟩
      · simpa only [hqval,List.getD_eq_getElem queries.val 0#u32 hiLen] using hr
      · rw [extend_success flat flat1 s hf,hsval]
      · have heq := UScalar.add_equiv i 1#usize
        rw [hj] at heq
        simpa only [show (1#usize).val = 1 from rfl] using heq.2.1
  · simp only [hi,ite_false] at h
    cases h

#print axioms body_done_none
#print axioms body_no_done_ok
#print axioms body_cont
end AspisR1GeometryInputs.Proof
