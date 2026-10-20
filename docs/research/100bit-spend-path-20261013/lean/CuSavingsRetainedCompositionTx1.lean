import CuSavingsRetainedCompositionTx1Transport
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionTx1
attribute [local irreducible] CuSavingsRetainedCompositionTx1Transport.finishNew CuSavingsRetainedCompositionTx1Transport.finishOld
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedCompositionTx1Transport
variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks] [RetainedPrefix]

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (m >>= f)=.ok out) : ∃ x,m=.ok x ∧ f x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

private theorem bind_ext {A B : Type} (m : Result A) (f g : A → Result B)
    (h : ∀ x,m=.ok x → f x=g x) : (m >>= f)=(m >>= g) := by
  cases hm : m with
  | fail e => rfl
  | div => rfl
  | ok x => exact h x hm

/-- The actual complete source preparation caller supplies its own successful
preparation witness. No canonicality or child-success condition is assumed. -/
theorem preparation_origins {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial final : Array aspis_core.field.WideExact 29#usize)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize) (p : verifier.Prepared)
    (h : retained.tx1_prepare D publicValue v hash obs initial=.ok (.Ok (claims,p),final)) :
    ∃ sem,r1_semantic.verify_observed D publicValue v.semantic hash obs=.ok (.Ok sem) ∧
      gamma_new.Prepared.gamma_new_new D sem v hash initial=.ok (.Ok p,final) := by
  unfold retained.tx1_prepare at h
  obtain ⟨semantic,hsemantic,h⟩ := bind_ok _ _ _ h
  cases semantic with
  | Err error =>
    simp only [core.result.Result.map_err,AspisR1PublicPreparation.core.result.Result.map_err,bind_tc_ok,
      retained.tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
      retained.tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok sem =>
    simp only [core.result.Result.map_err,AspisR1PublicPreparation.core.result.Result.map_err,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨entry,hprep,h⟩ := bind_ok _ _ _ h
    rcases entry with ⟨result,g⟩
    simp only [uncurry_apply_pair] at h
    cases result with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok p1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      have he := Result.ok.inj h
      have hp := congrArg (fun entry => entry.1) he
      have hg := congrArg Prod.snd he
      have hpp := congrArg Prod.snd (core.result.Result.Ok.inj hp)
      change p1=p at hpp
      change g=final at hg
      exact ⟨sem,hsemantic,by simpa only [hpp,hg] using hprep⟩

/-- Projection retained for the rho caller bridge. -/
theorem preparation_witness {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (v : verifier.View) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (initial final : Array aspis_core.field.WideExact 29#usize)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize) (p : verifier.Prepared)
    (h : retained.tx1_prepare D publicValue v hash obs initial=.ok (.Ok (claims,p),final)) :
    ∃ sem,gamma_new.Prepared.gamma_new_new D sem v hash initial=.ok (.Ok p,final) := by
  obtain ⟨sem,_,hprep⟩ := preparation_origins D publicValue v hash obs initial final claims p h
  exact ⟨sem,hprep⟩

variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]
  [AspisR1RhoResumeCaller.ResumeCommon] [AspisR1RhoTransactions.TxCommon]

/-- Complete original post-gamma tx1 caller composed with the actual rho
replacement. Parse/semantic/preparation/allocation/observer failures and
divergence are preserved; successful branches derive all rho entry invariants
from the actual source producer executions. -/
theorem source_tx1_rho_equivalence {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (backend : CuSavingsRhoEmptyReserveModel.Backend)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val) :
    letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
    retained.tx1 (finishNew start len cursor) D publicValue publicBytes proof k hash obs=
      retained.tx1 (finishOld start len cursor) D publicValue publicBytes proof k hash obs := by
  letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
  unfold retained.tx1
  split
  · rfl
  · rename_i hk
    have hkval : k.val ≤ 22 := by scalar_tac
    apply bind_ext
    intro parsed _
    cases parsed with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    | Ok v =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply bind_ext
      intro marked _
      cases marked
      apply bind_ext
      intro preparation hp
      rcases preparation with ⟨result,g⟩
      simp only [uncurry_apply_pair]
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      | Ok val =>
        rcases val with ⟨claims,p⟩
        obtain ⟨sem,hprep⟩ := preparation_witness D publicValue v hash obs _ g claims p hp
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,uncurry_apply_pair]
        apply bind_ext
        intro allocated ha
        cases allocated with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        | Ok acc =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply bind_ext
          intro marked _
          cases marked
          have he := CuSavingsRhoCallerClosure.fresh_source_equivalence (digest D) D sem v hash
            _ g p backend acc hprep ha start len cursor future h64 hfree
            (view v) publicBytes proof k obs hkval
          unfold finishNew finishOld
          rw [he]

#print axioms preparation_origins
#print axioms preparation_witness
#print axioms source_tx1_rho_equivalence
end AspisR1.CuSavingsRetainedCompositionTx1
