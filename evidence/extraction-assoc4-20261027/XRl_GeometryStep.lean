import XRl_GeometryCollect
import XRl_GeometryVectors
import XRl_SliceRemaining
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools
namespace XRl_GeometryStep
abbrev State := core.slice.iter.Iter U32 × alloc.vec.Vec aspis_core.field.M31 × alloc.vec.Vec aspis_core.field.M31
def post (n : Nat) (r : core.result.Result verifier.QueryGeometry verifier.Error) : Prop :=
  match r with | .Ok g => g.line_z.val.length=n ∧ g.inverses.val.length=n | .Err _ => True
def Inv (n : Nat) (it : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec aspis_core.field.M31) : Prop :=
  lines.val.length+XRk_GeometryMeasure.remaining it=n ∧ flat.val.length=5*lines.val.length
def measure (s : State) : Nat := XRk_GeometryMeasure.remaining s.1

theorem step (n : Nat) (start : Usize) (it : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec aspis_core.field.M31)
    (out : ControlFlow State (core.result.Result verifier.QueryGeometry verifier.Error))
    (shape : Inv n it lines flat)
    (run : verifier.QueryGeometry.for_range_loop0.body start it lines flat=ok out) :
    match out with
    | .done r => post n r
    | .cont next => Inv n next.1 next.2.1 next.2.2 ∧ measure next < measure (it,lines,flat) := by
  unfold verifier.QueryGeometry.for_range_loop0.body at run
  obtain ⟨value,next,hnext,run⟩ := pair_bind_success _ _ _ run
  cases value with
  | none =>
    have remaining := XRl_SliceRemaining.terminal it next hnext
    obtain ⟨empty,hempty,run⟩ := bind_success _ _ _ run
    have emptyEq : empty=flat.val.isEmpty := (Result.ok.inj hempty).symm
    subst empty
    split at run
    · rename_i hempty
      have same := Result.ok.inj run
      subst out
      have flatnil : flat.val=[] := List.isEmpty_iff.mp hempty
      have zero : flat.val.length=0 := by rw [flatnil]; rfl
      change lines.val.length=n ∧ 0=n
      rcases shape with ⟨shape0,shape1⟩
      constructor <;> omega
    · obtain ⟨prefixes,product,_,run⟩ := pair_bind_success _ _ _ run
      obtain ⟨inverse,_,run⟩ := bind_success _ _ _ run
      obtain ⟨zero,_,run⟩ := bind_success _ _ _ run
      obtain ⟨resized,_,run⟩ := bind_success _ _ _ run
      obtain ⟨reversed,_,run⟩ := bind_success _ _ _ run
      obtain ⟨inverted,_,run⟩ := bind_success _ _ _ run
      obtain ⟨mapped,hmap,run⟩ := bind_success _ _ _ run
      obtain ⟨inverses,hinv,run⟩ := bind_success _ _ _ run
      have same := Result.ok.inj run
      subst out
      have cardinal := XRl_GeometryCollect.length mapped inverses hinv
      have mapEq := Result.ok.inj hmap
      subst mapped
      change inverses.val.length=lines.val.length-0 at cardinal
      dsimp only [post]
      rcases shape with ⟨shape0,shape1⟩
      constructor <;> omega
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
          · obtain ⟨flat1,hflat1,run⟩ := bind_success _ _ _ run
            obtain ⟨lines1,hlines1,run⟩ := bind_success _ _ _ run
            have same := Result.ok.inj run
            subst out
            have lineSize := XRk_VectorLength.push lines lines1 lineZ hlines1
            have flatSize := congrArg List.length (XRl_GeometryVectors.extend flat flat1 _ hflat1)
            rw [List.length_append] at flatSize
            change flat1.val.length=flat.val.length+5 at flatSize
            have remSize := XRl_SliceRemaining.advance it next query hnext
            refine ⟨?_,XRk_GeometryMeasure.advance it next query hnext⟩
            rcases shape with ⟨shape0,shape1⟩
            constructor <;> dsimp only [Inv] <;> omega
#print axioms step
end XRl_GeometryStep
