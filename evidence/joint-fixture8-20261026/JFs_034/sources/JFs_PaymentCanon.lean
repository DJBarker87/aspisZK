import JFu_DigestCheck
set_option autoImplicit false
namespace AspisR1.JFs_PaymentCanon
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

theorem source (digest : Array U32 8#usize) (canon : JFu_DigestCanonical.Canonical digest) :
    pool_v1.payment_relation.digest_is_canonical digest=ok true := by
  have spec : pool_v1.payment_relation.digest_is_canonical digest ⦃ b => b=true ⦄ := by
    unfold pool_v1.payment_relation.digest_is_canonical
      pool_v1.payment_relation.digest_is_canonical_loop
    refine loop.spec_decr_nat
      (fun i : Usize => 8-i.val) (fun i : Usize => i.val≤8)
      (fun b : Bool => b=true)
      (fun i => pool_v1.payment_relation.digest_is_canonical_loop.body digest i) 0#usize ?_ ?_
    · intro i hi
      unfold pool_v1.payment_relation.digest_is_canonical_loop.body
      step*
      all_goals first
        | scalar_tac
        | (have hc:=canon ⟨i.val,by scalar_tac⟩
           unfold aspis_core.field.P at *
           simp_all [JFu_DigestCanonical.Canonical]
           scalar_tac)
    · scalar_tac
  obtain ⟨b,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end AspisR1.JFs_PaymentCanon
