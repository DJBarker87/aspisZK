import S9ActualDotBackendMapV1
import EbyKCheckedQCanonicality
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualEbyKBackendTransportV1
abbrev NativeW := aspis_core.field.wide_exact.WideExact
abbrev NativeQ := aspis_core.field.QM31
abbrev SourceState := AspisR1EbyKPushDotBackend.PushState
abbrev SourceW := AspisR1EbyKPushDotBackend.PushWide
abbrev SourceQ := AspisR1EbyKPushDotBackend.PushQm

def toSourceDot (d : fast_pairing.canonical.Dot) : AspisR1EbyKPushDotBackend.PushDot := ⟨d.sums⟩
def toSourceState (s : fast_pairing.EbyKDot) : SourceState :=
  {c0:=toSourceDot s.c0,c1:=toSourceDot s.c1,count:=s.count}
def toSourceQ (q : NativeQ) : SourceQ :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}
def toSourceWide (w : NativeW) : SourceW := {c0:=toSourceQ w.c0,c1:=toSourceQ w.c1}

private theorem ix0 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=.ok a := rfl
private theorem ix1 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=.ok b := rfl
private theorem ix2 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=.ok c := rfl
private theorem ix3 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=.ok d := rfl

/-- The actual native checked scalar's SAME accepted words pass the retained
concrete S5 short-circuit scanner. No separately assumed scalar canonicality. -/
theorem native_checked_q_success_to_source (scalar : NativeQ) (q : Array U32 4#usize)
    (h : fast_pairing.checked_q scalar=.ok(.Ok q)) :
    AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll (toSourceQ scalar)=.ok(.Ok q) := by
  unfold fast_pairing.checked_q fast_pairing.limbs_of at h
  simp only [bind_tc_ok] at h
  unfold fast_pairing.canonical.Q.from_limbs at h
  simp only [ix0,ix1,ix2,ix3,bind_tc_ok] at h
  split at h
  · rename_i h0
    split at h
    · rename_i h1
      split at h
      · rename_i h2
        split at h
        · rename_i h3
          have hq := core.result.Result.Ok.inj (Result.ok.inj h)
          subst q
          unfold AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
          simp only [AspisR1EbyKCheckedQAllParamV1.limbsOf,toSourceQ,bind_tc_ok]
          rw [AspisR1EbyKCheckedQConcreteAll.fromLimbs_model_eq]
          simp [AspisR1EbyKCheckedQConcreteAll.allRun,
            AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut,
            AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureCallMut,
            AspisR1EbyKCheckedQAllParamV1.P,fast_pairing.canonical.P,
            AspisR1EbyKCheckedQAllParamV1.optionOkOr,Array.make,h0,h1,h2,h3]
        · cases h
      · cases h
    · cases h
  · cases h

#print axioms native_checked_q_success_to_source
end AspisR1S9ActualEbyKBackendTransportV1
