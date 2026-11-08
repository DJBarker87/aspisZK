import NNG_Model345
import NMT_R2_ValidatorTotal
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ValidatorGraph345
open Aeneas Aeneas.Std NMT_345 RSL

def native (st : Statement) :=
 mapOuter (mapCore id (fun _ : FormatError => (PE.InvalidAccountData))) (validateCall st)

theorem observation (st : Statement) :
 NMT_R2_EmittedData.observe id (native st)=NNG_Pure345.check (!LIBC_S1.valid st) .invalidAccountData := by
 unfold native LIBC_S1.valid
 rw [NMT_R2_ValidatorTotal.emitted]
 cases NMT_R2_ValidatorTotal.fresh st with
 | Ok u=>cases u;rfl
 | Err e=>rfl
#print axioms observation

theorem law (st : Statement) (env : Env) :
 RS.check (!LIBC_S1.valid st) .invalidAccountData env (NMT_R2_EmittedData.observe id (native st)) := by
 rw [observation]
 exact NNG_Pure345.check_valid _ _ env
#print axioms law
end AspisR1.NNG_ValidatorGraph345
