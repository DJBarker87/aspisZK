import XRk_GeometryMeasure
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools
namespace XRk_GeometryStep
abbrev State := core.slice.iter.Iter U32 × alloc.vec.Vec aspis_core.field.M31 × alloc.vec.Vec aspis_core.field.M31
def post (start : Usize) (r : core.result.Result verifier.QueryGeometry verifier.Error) : Prop :=
  match r with | .Ok g => g.start=start | .Err _ => True
def measure (s : State) : Nat := XRk_GeometryMeasure.remaining s.1

theorem step (start : Usize) (it : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec aspis_core.field.M31)
    (out : ControlFlow State (core.result.Result verifier.QueryGeometry verifier.Error))
    (run : verifier.QueryGeometry.for_range_loop0.body start it lines flat=ok out) :
    match out with
    | .done r => post start r
    | .cont next => measure next < measure (it,lines,flat) := by
  unfold verifier.QueryGeometry.for_range_loop0.body at run
  obtain ⟨value,next,hnext,run⟩ := pair_bind_success _ _ _ run
  cases value with
  | none =>
    obtain ⟨empty,_,run⟩ := bind_success _ _ _ run
    split at run
    · have same := Result.ok.inj run
      subst out
      rfl
    · obtain ⟨prefixes,product,_,run⟩ := pair_bind_success _ _ _ run
      obtain ⟨inverse,_,run⟩ := bind_success _ _ _ run
      obtain ⟨zero,_,run⟩ := bind_success _ _ _ run
      obtain ⟨resized,_,run⟩ := bind_success _ _ _ run
      obtain ⟨reversed,_,run⟩ := bind_success _ _ _ run
      obtain ⟨inverted,_,run⟩ := bind_success _ _ _ run
      obtain ⟨mapped,_,run⟩ := bind_success _ _ _ run
      obtain ⟨inverses,_,run⟩ := bind_success _ _ _ run
      have same := Result.ok.inj run
      subst out
      rfl
  | some query =>
    obtain ⟨u,_,run⟩ := bind_success _ _ _ run
    obtain ⟨ru,_,run⟩ := bind_success _ _ _ run
    obtain ⟨r,_,run⟩ := bind_success _ _ _ run
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      have same := Result.ok.inj run
      subst out
      trivial
    | Ok fibre =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨point,_,run⟩ := bind_success _ _ _ run
      obtain ⟨group,_,run⟩ := bind_success _ _ _ run
      obtain ⟨first,_,run⟩ := bind_success _ _ _ run
      obtain ⟨rx,_,run⟩ := bind_success _ _ _ run
      obtain ⟨r,_,run⟩ := bind_success _ _ _ run
      cases r with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at run
        have same := Result.ok.inj run
        subst out
        trivial
      | Ok fibreX =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        obtain ⟨lineX,_,run⟩ := bind_success _ _ _ run
        obtain ⟨again,_,run⟩ := bind_success _ _ _ run
        obtain ⟨last,_,run⟩ := bind_success _ _ _ run
        obtain ⟨ry,_,run⟩ := bind_success _ _ _ run
        obtain ⟨r,_,run⟩ := bind_success _ _ _ run
        cases r with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,bind_tc_ok] at run
          have same := Result.ok.inj run
          subst out
          trivial
        | Ok fibreY =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
          obtain ⟨lineY,_,run⟩ := bind_success _ _ _ run
          obtain ⟨square,_,run⟩ := bind_success _ _ _ run
          obtain ⟨double,_,run⟩ := bind_success _ _ _ run
          obtain ⟨one,_,run⟩ := bind_success _ _ _ run
          obtain ⟨lineZ,_,run⟩ := bind_success _ _ _ run
          try simp only [lift,bind_tc_ok] at run
          obtain ⟨iter,_,run⟩ := bind_success _ _ _ run
          obtain ⟨zero,ignored,_,run⟩ := pair_bind_success _ _ _ run
          split at run
          · have same := Result.ok.inj run
            subst out
            trivial
          · obtain ⟨flat1,_,run⟩ := bind_success _ _ _ run
            obtain ⟨lines1,_,run⟩ := bind_success _ _ _ run
            have same := Result.ok.inj run
            subst out
            exact XRk_GeometryMeasure.advance it next query hnext
#print axioms step
end XRk_GeometryStep
