import CurrentClaimCallerComposition
import CurrentFinishField
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParser
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE
abbrev E := Concrete.E

def fromFinish (x : FinishE) : E :=
  Concrete.fromFull (AspisR1CurrentWide.Proof.ofFinishE x)

theorem canonical_from_finish (x : FinishE)
    (hx : AspisR1CurrentWide.Proof.CanonicalFinish x) : Concrete.Canonical (fromFinish x) := by
  simpa only [Concrete.Canonical,fromFinish,Concrete.to_from,AspisR1CurrentWide.Proof.CanonicalFinish] using hx

theorem decode_from_finish (x : FinishE) :
    Concrete.decode (fromFinish x) = AspisR1CurrentWide.Proof.decodeFinish x := by
  simp only [Concrete.decode,fromFinish,Concrete.to_from,AspisR1CurrentWide.Proof.decodeFinish]

def field (bytes : Slice U8) (i : Usize) : Result E := do
  let x ← AspisR1CurrentWide.Proof.finishField bytes i
  ok (fromFinish x)

def c0 (x : E) : Result aspis_core.field.QM31 := .ok x.c0

def withParser {D : Type} (ops : ClaimDotOps D) : ClaimDotOps D :=
  {ops with field:=field, c0:=c0}

theorem field_success (bytes : Slice U8) (i : Usize) (out : E)
    (h : field bytes i = .ok out) :
    Concrete.Canonical out ∧ ∃ x, AspisR1CurrentWide.Proof.finishField bytes i=.ok x ∧
      out=fromFinish x ∧ Concrete.decode out=AspisR1CurrentWide.Proof.decodeFinish x := by
  unfold field at h
  cases hr : AspisR1CurrentWide.Proof.finishField bytes i with
  | fail e => simp only [hr,bind_tc_fail] at h; cases h
  | div => simp only [hr,bind_tc_div] at h; cases h
  | ok x =>
    simp only [hr,bind_tc_ok] at h
    have he := Result.ok.inj h
    subst out
    exact ⟨canonical_from_finish x (AspisR1CurrentWide.Proof.finishField_success_canonical bytes i x hr),
      x,rfl,rfl,decode_from_finish x⟩

theorem c0_success_canonical (x : E) (hx : Concrete.Canonical x)
    (out : aspis_core.field.QM31) (h : c0 x=.ok out) :
    out=x.c0 ∧ AspisR1CurrentWide.Proof.CanonicalQM (Concrete.toQM out) := by
  have he := Result.ok.inj h
  subst out
  exact ⟨rfl,hx.1⟩

#print axioms canonical_from_finish
#print axioms decode_from_finish
#print axioms field_success
#print axioms c0_success_canonical
end AspisR1CurrentPreparedClaim.ClaimParser
