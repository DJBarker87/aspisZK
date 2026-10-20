import CuSavingsGeometryCaller
import CuSavingsRhoQuery
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryCounter
open Aeneas Aeneas.Std Result AspisR1RhoQuery
open CuSavingsGeometryCaller
variable [AspisR1RhoAccumulate.AccumulateCommon] [QueryCommon]

private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

/-- The actual source accumulator's successful checked suffix advances the
counter; no field-value canonicality or child-success premise is required. -/
theorem accumulation_next (p : verifier.Prepared) (a out : verifier.Accumulator)
    (node : aspis_core.field.M31) (value : aspis_core.field.WideExact)
    (hi : a.next.val<22)
    (h : factored_old.accumulate_with_node p a node value=.ok out) :
    out.next.val=a.next.val+1 := by
  unfold factored_old.accumulate_with_node AspisR1RhoAccumulate.factored_old.accumulate_with_node at h
  obtain ⟨basis,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨weights,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨product,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨rhs,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨power,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨next,hnext,h⟩ := bind_ok _ _ _ h
  have heq := Result.ok.inj h
  have hout : out.next=next := (congrArg AspisR1RhoAccumulate.verifier.Accumulator.next heq).symm
  obtain ⟨expected,hs,hv⟩ := CuSavingsRhoPowerTail.next_success a.next hi
  have hn : next=expected := Result.ok.inj (hnext.symm.trans hs)
  rw [hout,hn]
  exact hv

/-- The complete actual source query supplies the increment certificate used
by the enclosing source-loop range induction. Earlier failures never create
a successful next-call witness. -/
theorem query_next {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase→Result Unit)) (geometry : QueryGeometry)
    (hi : a.next.val<22)
    (h : query_old.query_with_geometry digest v p a g hash obs geometry=.ok (.Ok out)) :
    out.next.val=a.next.val+1 := by
  unfold query_old.query_with_geometry at h
  obtain ⟨r,_,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok pair =>
    rcases pair with ⟨u,folded⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,uncurry_apply_pair] at h
    obtain ⟨node,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨after,ha,h⟩ := bind_ok _ _ _ h
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    have heq := core.result.Result.Ok.inj (Result.ok.inj h)
    subst out
    exact accumulation_next p a after node folded hi ha

theorem successful_query_reachable {H : Type} (digest : aspis_core.Digest32 H)
    (v : verifier.View) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase→Result Unit)) (geometry : QueryGeometry)
    (start finish : Usize) (hreach : Calls start a.next)
    (he : finish.val≤22) (guard : a.next<finish)
    (h : query_old.query_with_geometry digest v p a g hash obs geometry=.ok (.Ok out)) :
    Calls start out.next := by
  have hi : a.next.val<22 := by change a.next.val<finish.val at guard;omega
  exact Calls.advance hreach (query_next digest v p a out g hash obs geometry hi h)

#print axioms accumulation_next
#print axioms query_next
#print axioms successful_query_reachable
end AspisR1.CuSavingsGeometryCounter
