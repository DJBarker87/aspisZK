import S4ReverseBatchBodyRootV1
import S4ReverseOuterHeadLoopRootV1
import S4InstalledReverseHelperRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsConcreteReverseHeadRootV1
open AspisR1FastDotsCurrent
abbrev Ops := FourDotsOps
abbrev Wide := aspis_core.field.wide_exact.WideExact
abbrev TermOldBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.OldBody
abbrev TermNewBody := AspisR1FastDotsNewTermBodyOldBodyBridgeV1.NewBody
abbrev Range := core.ops.range.Range Usize
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev install := AspisR1FastDotsFourCallbacksForwardRootV1.install

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : (r >>= f) = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem old_term_body_done_fixed_body
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : Range) (sums out : Array U64 8#usize)
    (hbody : TermOldBody ops q g slot iter sums = .ok (.done out)) :
    TermNewBody ops q g slot iter sums = .ok (.done out) := by
  unfold TermOldBody AspisR1FastDotsNewTermBodyOldBodyBridgeV1.OldBody at hbody
  obtain ⟨⟨o,it⟩,hnext,hrest⟩ := bind_ok_inv hbody
  cases o with
  | none =>
    have heq : sums = out := ControlFlow.done.inj (Result.ok.inj hrest)
    subst out
    unfold TermNewBody AspisR1FastDotsNewTermBodyOldBodyBridgeV1.NewBody
    rw [hnext]
    rfl
  | some term =>
    repeat' (first | obtain ⟨_,_,hrest⟩ := bind_ok_inv hrest)
    cases Result.ok.inj hrest

#print axioms old_term_body_done_fixed_body
end AspisR1FastDotsConcreteReverseHeadRootV1
