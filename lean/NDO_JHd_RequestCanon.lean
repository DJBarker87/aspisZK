import NDO_JFu_DigestCheck
import JHd_RequestFuns
set_option autoImplicit false
namespace AspisR1.JHd_RequestCanon
open Aeneas Aeneas.Std Result WP
open AspisR20Request

theorem source (digest : Array U32 8#usize) (canon : JFu_DigestCanonical.Canonical digest) :
    pool_v1.payment_relation.digest_is_canonical digest=ok true := by
  have c0:=canon ⟨0,by decide⟩
  have c1:=canon ⟨1,by decide⟩
  have c2:=canon ⟨2,by decide⟩
  have c3:=canon ⟨3,by decide⟩
  have c4:=canon ⟨4,by decide⟩
  have c5:=canon ⟨5,by decide⟩
  have c6:=canon ⟨6,by decide⟩
  have c7:=canon ⟨7,by decide⟩
  have spec : pool_v1.payment_relation.digest_is_canonical digest ⦃ b => b=true ⦄ := by
    unfold pool_v1.payment_relation.digest_is_canonical
    step*
    all_goals unfold aspis_core.field.P at *
    all_goals simp_all [JFu_DigestCanonical.Canonical]
    all_goals scalar_tac
  obtain ⟨b,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end AspisR1.JHd_RequestCanon
