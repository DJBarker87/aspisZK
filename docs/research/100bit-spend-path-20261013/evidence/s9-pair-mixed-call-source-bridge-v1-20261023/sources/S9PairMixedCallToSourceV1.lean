import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9SquareMulQMCutV1.Funs
import S9CombinedWideMulQM31CurrentOuterV1
import S9PairCallerStepOperationBridgeV1
import S3S9ConcreteFieldOpsV1
import KpowersCurrentQMSemanticsV1
import S9SourceResultTransportV1
import S9CombinedWideMulQM31HelperMapV1
import S9ResultSuccessReflectionV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedCallToSourceV1

abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PairW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev SrcQ := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev SrcW := AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact
abbrev CurQ := AspisR1CurrentWide.field.QM31
abbrev CurW := AspisR1CurrentWide.field.wide_exact.WideExact

def pairToSrcCM (x : AspisR1S9PairCallerStepV1.field.CM31) :
    AspisR1S9SquareMulQMCutV1.field.CM31 := ⟨x.a, x.b⟩
def pairToSrcQ (x : PairQ) : SrcQ := ⟨pairToSrcCM x.c0, pairToSrcCM x.c1⟩
def pairToSrcW (x : PairW) : SrcW := ⟨pairToSrcQ x.c0, pairToSrcQ x.c1⟩

def srcToPairCM (x : AspisR1S9SquareMulQMCutV1.field.CM31) :
    AspisR1S9PairCallerStepV1.field.CM31 := ⟨x.a, x.b⟩
def srcToPairQ (x : SrcQ) : PairQ := ⟨srcToPairCM x.c0, srcToPairCM x.c1⟩
def srcToPairW (x : SrcW) : PairW := ⟨srcToPairQ x.c0, srcToPairQ x.c1⟩

def pairToCurrentCM (x : AspisR1S9PairCallerStepV1.field.CM31) :
    AspisR1CurrentWide.field.CM31 := ⟨x.a, x.b⟩
def pairToCurrentQ (x : PairQ) : CurQ := ⟨pairToCurrentCM x.c0, pairToCurrentCM x.c1⟩
def pairToCurrentW (x : PairW) : CurW := ⟨pairToCurrentQ x.c0, pairToCurrentQ x.c1⟩

def srcToCurrentCM (x : AspisR1S9SquareMulQMCutV1.field.CM31) :
    AspisR1CurrentWide.field.CM31 := ⟨x.a, x.b⟩
def srcToCurrentQ (x : SrcQ) : CurQ := ⟨srcToCurrentCM x.c0, srcToCurrentCM x.c1⟩
def srcToCurrentW (x : SrcW) : CurW := ⟨srcToCurrentQ x.c0, srcToCurrentQ x.c1⟩

def mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

private theorem pairToCurrent_eq_srcToCurrent_pair (x : PairW) :
    pairToCurrentW x = srcToCurrentW (pairToSrcW x) := by
  cases x <;> rfl

private theorem pairToCurrentQ_eq_srcToCurrent_pair (x : PairQ) :
    pairToCurrentQ x = srcToCurrentQ (pairToSrcQ x) := by
  cases x <;> rfl

private theorem pairToCurrent_eq_helperMap (x : PairW) :
    pairToCurrentW x = AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
      (AspisR1S9PairCallerStepV1.toP6W x) := by
  cases x with
  | mk c0 c1 => cases c0 <;> cases c1 <;> rfl

private theorem pairToCurrentQ_eq_helperMap (x : PairQ) :
    pairToCurrentQ x = AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (AspisR1S9PairCallerStepV1.toP6Q x) := by
  cases x with
  | mk c0 c1 => cases c0 <;> cases c1 <;> rfl

private theorem pairToCurrent_injective : Function.Injective pairToCurrentW := by
  let currentToPairCM (x : AspisR1CurrentWide.field.CM31) :
      AspisR1S9PairCallerStepV1.field.CM31 := ⟨x.a, x.b⟩
  let currentToPairQ (x : CurQ) : PairQ :=
    ⟨currentToPairCM x.c0, currentToPairCM x.c1⟩
  let currentToPairW (x : CurW) : PairW :=
    ⟨currentToPairQ x.c0, currentToPairQ x.c1⟩
  have hleft (x : PairW) : currentToPairW (pairToCurrentW x) = x := by
    cases x <;> rfl
  intro x y h
  have := congrArg currentToPairW h
  rw [hleft, hleft] at this
  exact this

private theorem mapResult_comp {A B C : Type} (f : A → B) (g : B → C)
    (r : Result A) :
    mapResult g (mapResult f r) = mapResult (g ∘ f) r := by
  cases r <;> rfl

private theorem mapResult_injective {A B : Type} (f : A → B)
    (hf : Function.Injective f) (r s : Result A)
    (h : mapResult f r = mapResult f s) : r = s := by
  cases r with
  | ok x => cases s with
    | ok y => exact congrArg Result.ok (hf (Result.ok.inj h))
    | fail e => cases h
    | div => cases h
  | fail e => cases s with
    | ok y => cases h
    | fail e' => cases Result.fail.inj h; rfl
    | div => cases h
  | div => cases s with
    | ok y => cases h
    | fail e => cases h
    | div => rfl

private theorem currentToHelperQM_helperToCurrentQM
    (x : AspisR1S9HelperP6.field.QM31) :
    AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x) = x := by
  cases x with
  | mk c0 c1 => cases c0 <;> cases c1 <;> rfl

private theorem mapResult_pairComp (r : Result SrcW) :
    mapResult pairToCurrentW (mapResult srcToPairW r) = mapResult srcToCurrentW r := by
  have hfun : pairToCurrentW ∘ srcToPairW = srcToCurrentW := by
    funext z
    cases z <;> rfl
  calc
    mapResult pairToCurrentW (mapResult srcToPairW r) =
        mapResult (pairToCurrentW ∘ srcToPairW) r :=
          mapResult_comp srcToPairW pairToCurrentW r
    _ = mapResult srcToCurrentW r := by rw [hfun]

private theorem helperToCurrent_result_roundtrip (r : Result CurW) :
    mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
      (mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide r) = r := by
  cases r <;> simp only [mapResult, AspisR1S9SourceResultTransportV1.mapResult,
    AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide_currentToHelperWide]

/-- The frozen pair-caller mixed product operation and the extracted source-cut
operation have the same whole Result after the explicit nested carrier maps.
The only arithmetic premise is canonicality of the actual left operand; the
right operand is normalized by the extracted operation itself. -/
theorem pair_mul_qm31_eq_source
    (x : PairW) (q : PairQ)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (pairToCurrentW x)) :
    AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q =
      mapResult srcToPairW
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
          (pairToSrcW x) (pairToSrcQ q)) := by
  have hpair : mapResult pairToCurrentW
      (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
        (pairToCurrentW x) (pairToCurrentQ q) := by
    have hcall := AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul_qm31 x q
    have hcomp : pairToCurrentW =
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide ∘
          AspisR1S9PairCallerStepV1.toP6W) := by
      funext z
      exact pairToCurrent_eq_helperMap z
    calc
      mapResult pairToCurrentW
          (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q) =
        mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
          (mapResult AspisR1S9PairCallerStepV1.toP6W
            (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q)) := by
              rw [hcomp]
              exact (mapResult_comp AspisR1S9PairCallerStepV1.toP6W
                AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide _).symm
      _ = mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
          (@AspisR1S9HelperP6.FieldOps.wideMulQM31
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
            (AspisR1S9PairCallerStepV1.toP6W x)
            (AspisR1S9PairCallerStepV1.toP6Q q)) :=
              congrArg (mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide) hcall
      _ = mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
          (AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation
            (AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide (pairToCurrentW x))
            (AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM (pairToCurrentQ q))) := by
              rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideMulQM31_dispatch]
              rw [pairToCurrent_eq_helperMap x, pairToCurrentQ_eq_helperMap q]
              rw [AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide_helperToCurrentWide,
                currentToHelperQM_helperToCurrentQM]
              rfl
      _ = mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide
          (mapResult AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide
            (AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
              (pairToCurrentW x) (pairToCurrentQ q))) := by
              have hwide :
                  AspisR1S9HelperP6PowerSemanticsV1.currentToHelperWide =
                    AspisR1S9CombinedWideMulQM31HelperMapV1.currentToHelperWide := by
                funext z
                cases z <;> rfl
              have hqm :
                  AspisR1S9HelperP6PowerSemanticsV1.currentToHelperQM =
                    AspisR1S9CombinedWideMulQM31HelperMapV1.currentToHelperQM := rfl
              rw [hwide, hqm]
              exact congrArg
                (mapResult AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentWide)
                (AspisR1S9CombinedWideMulQM31HelperMapV1.generated_helper_matches_current
                  (pairToCurrentW x) (pairToCurrentQ q))
      _ = AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
          (pairToCurrentW x) (pairToCurrentQ q) :=
              helperToCurrent_result_roundtrip _
  have hsourceInput :
      AspisR1S9CombinedWideMulQM31CurrentOuterV1.toCurrentWide (pairToSrcW x) =
        pairToCurrentW x := by
    cases x <;> rfl
  have hsource :=
    AspisR1S9CombinedWideMulQM31CurrentOuterV1.combined_wide_mul_qm31_to_current
      (pairToSrcW x) (pairToSrcQ q) (by
        rw [hsourceInput]
        exact hx)
  have hsourceAtPair : mapResult pairToCurrentW
      (mapResult srcToPairW
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
          (pairToSrcW x) (pairToSrcQ q))) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
        (pairToCurrentW x) (pairToCurrentQ q) := by
    calc
      _ = mapResult srcToCurrentW
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
          (pairToSrcW x) (pairToSrcQ q)) :=
            mapResult_pairComp _
      _ = AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
          (srcToCurrentW (pairToSrcW x)) (srcToCurrentQ (pairToSrcQ q)) := by
            have hw : srcToCurrentW =
                AspisR1S9CombinedWideMulQM31CurrentOuterV1.toCurrentWide := by
              funext z
              cases z <;> rfl
            have hq : srcToCurrentQ =
                AspisR1S9CombinedWideMulQM31CurrentOuterV1.toCurrentQM := by
              funext z
              cases z <;> rfl
            have hmap := congrArg
              (fun f => AspisR1S9SourceResultTransportV1.mapResult f
                (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
                  (pairToSrcW x) (pairToSrcQ q))) hw
            change mapResult srcToCurrentW
              (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
                (pairToSrcW x) (pairToSrcQ q)) = _ at hmap
            have hsource' := hsource
            change AspisR1S9SourceResultTransportV1.mapResult
              AspisR1S9CombinedWideMulQM31CurrentOuterV1.toCurrentWide
              (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
                (pairToSrcW x) (pairToSrcQ q)) = _ at hsource'
            rw [← hw] at hsource'
            rw [← hq] at hsource'
            exact hmap.trans hsource'
      _ = AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
          (pairToCurrentW x) (pairToCurrentQ q) := by
            rw [← pairToCurrent_eq_srcToCurrent_pair x,
              ← pairToCurrentQ_eq_srcToCurrent_pair q]
  have hresult := mapResult_injective pairToCurrentW pairToCurrent_injective _ _
    (hpair.trans hsourceAtPair.symm)
  exact hresult

/-- A successful mixed-product bind from the caller has a source-cut success
with the same input operands and the exact output transported back to the
caller carrier. This consumes the caller's already-obtained bind witness; it
does not replay or assume a second successful operation. -/
theorem pair_mul_qm31_success_reflects_source
    (x : PairW) (q : PairQ) (out : PairW)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (pairToCurrentW x))
    (hcall : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q = .ok out) :
    ∃ sourceOut,
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (pairToSrcW x) (pairToSrcQ q) = .ok sourceOut ∧
      out = srcToPairW sourceOut := by
  have hmap :
      mapResult srcToPairW
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
          (pairToSrcW x) (pairToSrcQ q)) = .ok out := by
    rw [← pair_mul_qm31_eq_source x q hx]
    exact hcall
  have hmap' :
      AspisR1S9ResultSuccessReflectionV1.mapResult srcToPairW
        (AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
          (pairToSrcW x) (pairToSrcQ q)) = .ok out := by
    exact hmap
  rcases (AspisR1S9ResultSuccessReflectionV1.mapResult_ok_iff srcToPairW _ out).mp hmap' with
    ⟨sourceOut, hsource, hout⟩
  exact ⟨sourceOut, hsource, hout.symm⟩

#print axioms pair_mul_qm31_eq_source
#print axioms pair_mul_qm31_success_reflects_source

end AspisR1S9PairMixedCallToSourceV1
