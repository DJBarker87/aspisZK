import S9ActualProcessKindTensorReachedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualRegularKindsTraceV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

def KindCall (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  weights.process_kind self kind alpha f folds n ap0 ap1 scratch parts = .ok (.Ok (),scratchOut,partsOut)

def RegularTrace (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  if shared then
    ∃ (s1 s2 : Scratch) (p1 p2 : Parts),
      KindCall self 2#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      KindCall self 5#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      KindCall self 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 partsOut
  else
    ∃ (s1 s2 s3 s4 : Scratch) (p1 p2 p3 p4 : Parts),
      KindCall self 1#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      KindCall self 2#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      KindCall self 3#usize alpha f folds n ap0 ap1 s2 s3 p2 p3 ∧
      KindCall self 5#usize alpha f folds n ap0 ap1 s3 s4 p3 p4 ∧
      KindCall self 6#usize alpha f folds n ap0 ap1 s4 scratchOut p4 partsOut

/-- Exact successful source trace, with real intermediate scratch/parts.
Shared runs reach only2,5,6; unshared runs reach1,2,3,5,6. -/
theorem regular_success_trace
    (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (h : weights.process_regular_kinds self shared alpha f folds n ap0 ap1 scratch parts =
      .ok (.Ok (),scratchOut,partsOut)) :
    RegularTrace self shared alpha f folds n ap0 ap1 scratch scratchOut parts partsOut := by
  cases shared with
  | true =>
    unfold weights.process_regular_kinds at h
    simp only [↓reduceIte] at h
    obtain ⟨processed1,hc1,tail1⟩ := bind_success _ _ _ h
    rcases processed1 with ⟨r1,s1,p1⟩
    cases r1 with
    | Err error1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at tail1
      have herr : (core.result.Result.Err error1 : Outcome)=.Ok () :=
        congrArg Prod.fst (Result.ok.inj tail1)
      cases herr
    | Ok unit1 =>
      cases unit1
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail1
      obtain ⟨processed2,hc2,tail2⟩ := bind_success _ _ _ tail1
      rcases processed2 with ⟨r2,s2,p2⟩
      cases r2 with
      | Err error2 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at tail2
        have herr : (core.result.Result.Err error2 : Outcome)=.Ok () :=
          congrArg Prod.fst (Result.ok.inj tail2)
        cases herr
      | Ok unit2 =>
        cases unit2
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail2
        obtain ⟨processed3,hc3,tail3⟩ := bind_success _ _ _ tail2
        rcases processed3 with ⟨r3,s3,p3⟩
        cases r3 with
        | Err error3 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at tail3
          have herr : (core.result.Result.Err error3 : Outcome)=.Ok () :=
            congrArg Prod.fst (Result.ok.inj tail3)
          cases herr
        | Ok unit3 =>
          cases unit3
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail3
          have hlast : KindCall self 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 partsOut :=
            hc3.trans tail3
          unfold RegularTrace
          simp only [↓reduceIte]
          exact ⟨s1,s2,p1,p2,hc1,hc2,hlast⟩
  | false =>
    unfold weights.process_regular_kinds at h
    simp only [Bool.false_eq_true,↓reduceIte] at h
    obtain ⟨processed1,hc1,tail1⟩ := bind_success _ _ _ h
    rcases processed1 with ⟨r1,s1,p1⟩
    cases r1 with
    | Err error1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at tail1
      have herr : (core.result.Result.Err error1 : Outcome)=.Ok () :=
        congrArg Prod.fst (Result.ok.inj tail1)
      cases herr
    | Ok unit1 =>
      cases unit1
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail1
      obtain ⟨processed2,hc2,tail2⟩ := bind_success _ _ _ tail1
      rcases processed2 with ⟨r2,s2,p2⟩
      cases r2 with
      | Err error2 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at tail2
        have herr : (core.result.Result.Err error2 : Outcome)=.Ok () :=
          congrArg Prod.fst (Result.ok.inj tail2)
        cases herr
      | Ok unit2 =>
        cases unit2
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail2
        obtain ⟨processed3,hc3,tail3⟩ := bind_success _ _ _ tail2
        rcases processed3 with ⟨r3,s3,p3⟩
        cases r3 with
        | Err error3 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at tail3
          have herr : (core.result.Result.Err error3 : Outcome)=.Ok () :=
            congrArg Prod.fst (Result.ok.inj tail3)
          cases herr
        | Ok unit3 =>
          cases unit3
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail3
          obtain ⟨processed4,hc4,tail4⟩ := bind_success _ _ _ tail3
          rcases processed4 with ⟨r4,s4,p4⟩
          cases r4 with
          | Err error4 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at tail4
            have herr : (core.result.Result.Err error4 : Outcome)=.Ok () :=
              congrArg Prod.fst (Result.ok.inj tail4)
            cases herr
          | Ok unit4 =>
            cases unit4
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail4
            obtain ⟨processed5,hc5,tail5⟩ := bind_success _ _ _ tail4
            rcases processed5 with ⟨r5,s5,p5⟩
            cases r5 with
            | Err error5 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at tail5
              have herr : (core.result.Result.Err error5 : Outcome)=.Ok () :=
                congrArg Prod.fst (Result.ok.inj tail5)
              cases herr
            | Ok unit5 =>
              cases unit5
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail5
              have hlast : KindCall self 6#usize alpha f folds n ap0 ap1 s4 scratchOut p4 partsOut :=
                hc5.trans tail5
              unfold RegularTrace
              simp only [Bool.false_eq_true,↓reduceIte]
              exact ⟨s1,s2,s3,s4,p1,p2,p3,p4,hc1,hc2,hc3,hc4,hlast⟩

#print axioms regular_success_trace
end AspisR1S9ActualRegularKindsTraceV1
