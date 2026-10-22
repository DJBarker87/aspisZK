import CurrentClaimDotModel
import LoopPowersEarlyTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimPowers
open Concrete
abbrev PE := AspisR1LoopPowers.field.WideExact

def toCM (x : aspis_core.field.CM31) : AspisR1LoopPowers.field.CM31 := ⟨x.a,x.b⟩
def toQM (x : aspis_core.field.QM31) : AspisR1LoopPowers.field.QM31 := ⟨toCM x.c0,toCM x.c1⟩
def toPowers (x : E) : PE := ⟨toQM x.c0,toQM x.c1⟩
def fromCM (x : AspisR1LoopPowers.field.CM31) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def fromQM (x : AspisR1LoopPowers.field.QM31) : aspis_core.field.QM31 := ⟨fromCM x.c0,fromCM x.c1⟩
def fromPowers (x : PE) : E := ⟨fromQM x.c0,fromQM x.c1⟩
theorem decode_to (x : E) : AspisR1LoopPowers.decode (toPowers x)=decode x := rfl
theorem decode_from (x : PE) : decode (fromPowers x)=AspisR1LoopPowers.decode x := rfl
theorem canonical_to (x : E) : AspisR1LoopPowers.Canonical (toPowers x) ↔ Canonical x := Iff.rfl
theorem canonical_from (x : PE) : Canonical (fromPowers x) ↔ AspisR1LoopPowers.Canonical x := Iff.rfl

def mapArray {N : Usize} (a : Array PE N) : Array E N :=
  ⟨a.val.map fromPowers,by simpa only [List.length_map] using a.property⟩
def powers (N : Usize) (x : E) : Result (Array E N) := do
  let out ← AspisR1LoopPowers.weights.early_powers N (toPowers x)
  ok (mapArray out)

theorem powers_total_exact (N : Usize) (x : E) (hx : Canonical x) :
    ∃ out, powers N x = .ok out ∧
      ∀ j : Fin N.val,
        Canonical (out.val[j.val]'(by rw [out.property]; exact j.isLt)) ∧
        decode (out.val[j.val]'(by rw [out.property]; exact j.isLt))=decode x^j.val := by
  obtain ⟨out,ho,hp⟩ := AspisR1LoopPowers.early_powers_total_exact N (toPowers x) hx
  refine ⟨mapArray out,?_,?_⟩
  · simp only [powers,ho,bind_tc_ok]
  · intro j
    obtain ⟨hc,he⟩ := hp j
    constructor
    · simpa only [mapArray,List.getElem_map,canonical_from] using hc
    · simpa only [mapArray,List.getElem_map,decode_from,decode_to] using he

def withConcretePowers {D : Type} (ops : ClaimDotOps D) : ClaimDotOps D :=
  {ops with powers:=powers}

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x)=.ok v) : ∃ x, m=.ok x ∧ k x=.ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem successful_claim_supplies_exact_powers {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa out : E) (g : Array E 29#usize) (hk : Canonical kappa)
    (h : verifier.prepared_claim (withConcretePowers ops) inst sem y1 inactive g kappa=.ok (core.result.Result.Ok out)) :
    ∃ k : Array E 7#usize, ∃ parts : Array E 7#usize,
      (∀ j : Fin 7, Canonical (k.val[j.val]'(by rw [k.property]; exact j.isLt)) ∧
        decode (k.val[j.val]'(by rw [k.property]; exact j.isLt))=decode kappa^j.val) ∧
      Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize inactive=.ok parts ∧
      verifier.prepared_claim_loop (withConcretePowers ops) inst {start:=0#usize,«end»:=6#usize}
        sem y1 g k parts=.ok (core.result.Result.Ok out) := by
  obtain ⟨k,hpowers,hprop⟩ := powers_total_exact 7#usize kappa hk
  unfold verifier.prepared_claim at h
  change (do let ks ← powers 7#usize kappa; _)=.ok (core.result.Result.Ok out) at h
  rw [hpowers,bind_tc_ok] at h
  obtain ⟨parts,hparts,hloop⟩ := bind_success _ _ _ h
  exact ⟨k,parts,hprop,hparts,hloop⟩
#print axioms powers_total_exact
#print axioms successful_claim_supplies_exact_powers
end AspisR1CurrentPreparedClaim.ClaimPowers
