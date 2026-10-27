import XRu_PushTransport
import S7Kani3CallerTrace
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_PushDomain
open S7Kani2OwnedRowRefinement
/-- The actual row words, canonical scalar limbs and periodic phase imply
all four checked-add domains needed by the emitted push transport. -/
theorem row (x : Fin 4 → U64) (q : aspis_core.field.QM31) (m : U32) (terms : Nat)
 (canonical : ∀ k, (powerLimb (XRu_PushTransport.power q) k).val<2^31-1)
 (basis : m.val<2^31-1)
 (phase : ∀ k, S7Kani3PhaseInvariant.Phase terms (x k).val) :
 ∀ j raw, j.val<4 → Array.index_usize (makeRow x) j=ok raw →
 raw.val+(S7Kani2OwnedRow.limb (XRu_PushTransport.power q) j).val*m.val<2^64 := by
 intro j raw hj read
 let k : Fin 4 := ⟨j.val,hj⟩
 have hk : j.val=k.val := rfl
 have bound := S7OwnedP6ScalarProof.phase_bound (x k) (powerLimb (XRu_PushTransport.power q) k)
  m (terms%4) (Nat.mod_lt _ (by decide)) (canonical k) basis (phase k)
 clear_value k
 fin_cases k <;>
  (have ji : j=UScalar.ofNat _ (by scalar_tac) := UScalar.eq_of_val_eq hk
   subst j
   simp only [makeRow,Array.index_usize,Array.make] at read
   have eq := Result.ok.inj read
   subst raw
   simpa [S7Kani2OwnedRow.limb,powerLimb] using bound)
#print axioms row
end XRz_PushDomain
