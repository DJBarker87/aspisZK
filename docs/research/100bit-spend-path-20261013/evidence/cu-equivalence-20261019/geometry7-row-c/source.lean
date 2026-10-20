import CuSavingsGeometryNode
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryRow
open Aeneas Aeneas.Std Result AspisR1GeometryCandidate7
open CuSavingsGeometryNode

theorem row_equivalence (query : U32) : old.row query=new.row query := by rfl

private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

def Origin (query : U32) (z : M) : Prop :=
  ∃ u group aligned fibre x,
    lift (UScalar.cast .Usize query)=.ok u ∧
    (u / 4#usize : Result Usize)=.ok group ∧
    (group * 4#usize : Result Usize)=.ok aligned ∧
    r0.domain.FibreIndex.new aligned=.ok (.Ok fibre) ∧
    fast_domain.line_node fibre=.ok x ∧ step x=.ok z

theorem row_origin (query : U32) (values : Array M 5#usize) (z : M)
    (h : new.row query=.ok (.Ok (values,z))) :
    Origin query z ∧ values.val.getD 4 field.M31.ZERO=z := by
  unfold new.row at h
  obtain ⟨u,hu,h⟩ := bind_ok _ _ _ h
  obtain ⟨r,hr,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err error =>
    simp [core.result.Result.map_err,AspisR1ViewParseProbe.core.result.Result.map_err,
      new.row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
      new.row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | Ok fibre0 =>
    simp only [core.result.Result.map_err,AspisR1ViewParseProbe.core.result.Result.map_err,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨point,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨group,hgroup,h⟩ := bind_ok _ _ _ h
    obtain ⟨aligned,haligned,h⟩ := bind_ok _ _ _ h
    obtain ⟨r,hr,h⟩ := bind_ok _ _ _ h
    cases r with
    | Err error =>
      simp [core.result.Result.map_err,AspisR1ViewParseProbe.core.result.Result.map_err,
        new.row.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        new.row.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok fibre =>
      simp only [core.result.Result.map_err,AspisR1ViewParseProbe.core.result.Result.map_err,
        bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨x,hx,h⟩ := bind_ok _ _ _ h
      obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
      obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
      obtain ⟨r,_,h⟩ := bind_ok _ _ _ h
      cases r with
      | Err error =>
        simp [core.result.Result.map_err,AspisR1ViewParseProbe.core.result.Result.map_err,
          new.row.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
          new.row.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
      | Ok fibreY =>
        simp only [core.result.Result.map_err,AspisR1ViewParseProbe.core.result.Result.map_err,
          bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨y,_,h⟩ := bind_ok _ _ _ h
        obtain ⟨square,hsquare,h⟩ := bind_ok _ _ _ h
        obtain ⟨doubled,hdoubled,h⟩ := bind_ok _ _ _ h
        obtain ⟨cached,hcached,h⟩ := bind_ok _ _ _ h
        have horigin : Origin query cached := by
          refine ⟨u,group,aligned,fibre,x,hu,hgroup,haligned,hr,hx,?_⟩
          simp only [step,hsquare,hdoubled,hcached,bind_tc_ok]
        obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
        obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
        obtain ⟨checked,_,h⟩ := bind_ok _ _ _ h
        rcases checked with ⟨hit,after⟩
        simp only [uncurry_apply_pair] at h
        split at h
        · cases h
        · cases Result.ok.inj h
          exact ⟨horigin,rfl⟩

#print axioms row_equivalence
#print axioms row_origin
end AspisR1.CuSavingsGeometryRow
