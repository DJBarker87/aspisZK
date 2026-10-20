import CurrentClaimPowersInstance
import CurrentClaimParserInstance
import CurrentClaimCallerComposition
import FinishDotConcreteOps
import FinishDotSourceABI
import EbyKPushDotBackend
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5ClaimDotConcreteAdapter
open AspisR1CurrentPreparedClaim

abbrev PushState := AspisR1FinishDotSourceABI.PushState
abbrev PushWide := AspisR1EbyKPushDotBackend.PushWide
abbrev PushQm := AspisR1EbyKPushDotBackend.PushQm

def toPushQm (q : aspis_core.field.QM31) : PushQm :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def toPushWide (v : aspis_core.field.WideExact) : PushWide :=
  ⟨toPushQm v.c0,toPushQm v.c1⟩

def concreteOps (rawFn : AspisR1EbyKPushDotBackend.RawFn) : ClaimDotOps PushState :=
  { powers := ClaimPowers.powers
    field := ClaimParser.field
    c0 := ClaimParser.c0
    newDot := AspisR1FinishDotConcreteOps.sourceNewDot
    pushDot := fun s v q =>
      AspisR1EbyKPushDotBackend.pushWithDotBackend rawFn s (toPushWide v) (toPushQm q)
    finishDot := fun s => do
      let out ← AspisR1FinishDotSourceABI.finishFromPush s
      ok (ClaimParser.fromFinish out) }

theorem toPushQm_fields (q : aspis_core.field.QM31) :
    toPushQm q = ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩ := rfl

theorem toPushWide_fields (v : aspis_core.field.WideExact) :
    toPushWide v = ⟨toPushQm v.c0,toPushQm v.c1⟩ := rfl

theorem parser_finish_value_push_map (x : AspisR1CurrentPreparedClaim.ClaimParser.FinishE) :
    toPushWide (ClaimParser.fromFinish x) = AspisR1FinishDotConcreteOps.toPushWide x := rfl

theorem concreteOps_newDot (rawFn : AspisR1EbyKPushDotBackend.RawFn) :
    (concreteOps rawFn).newDot = AspisR1FinishDotConcreteOps.sourceNewDot := rfl

theorem concreteOps_pushDot (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (s : PushState) (v : aspis_core.field.WideExact) (q : aspis_core.field.QM31) :
    (concreteOps rawFn).pushDot s v q =
      AspisR1EbyKPushDotBackend.pushWithDotBackend rawFn s (toPushWide v) (toPushQm q) := rfl

theorem successful_concrete_claim_has_powered_chain {H : Type}
    (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive kappa out : aspis_core.field.WideExact)
    (g : Array aspis_core.field.WideExact 29#usize)
    (hk : Concrete.Canonical kappa)
    (h : verifier.prepared_claim
      (ClaimPowers.withConcretePowers (concreteOps rawFn)) inst sem y1 inactive g kappa =
      Result.ok (core.result.Result.Ok out)) :
    ∃ k : Array aspis_core.field.WideExact 7#usize,
      ∃ parts : Array aspis_core.field.WideExact 7#usize,
        (∀ j : Fin 7,
          Concrete.Canonical (k.val[j.val]'(by rw [k.property]; exact j.isLt)) ∧
          Concrete.decode (k.val[j.val]'(by rw [k.property]; exact j.isLt)) =
            Concrete.decode kappa ^ j.val) ∧
        Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO)
          0#usize inactive = Result.ok parts ∧
        AspisR1CurrentPreparedClaim.ClaimTrace.Chain
          (ClaimPowers.withConcretePowers (concreteOps rawFn)) inst sem y1 g k
          {start := 0#usize, «end» := 6#usize} parts out := by
  exact AspisR1CurrentPreparedClaim.ClaimTrace.successful_claim_has_powered_chain
    (concreteOps rawFn) inst sem y1 inactive kappa out g hk h

#print axioms toPushQm_fields
#print axioms toPushWide_fields
#print axioms parser_finish_value_push_map
#print axioms concreteOps_newDot
#print axioms concreteOps_pushDot
#print axioms successful_concrete_claim_has_powered_chain
end AspisR1S5ClaimDotConcreteAdapter
