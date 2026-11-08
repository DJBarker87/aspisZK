import NMX_R4_AccountProjection
set_option autoImplicit false
noncomputable section
namespace NMX_R4_ReadDecode
open RSL
open NMX_R4_AccountProjection (account)
open NMX_R3_RegistryByteCut (cut)

/-- The independent Box allocation follows a successful decoder at the same
bytes; cloned errors keep their original error and allocation stop prefix. -/
theorem boxed {A B : Type} (decode : Bytes → Option A)
 (law : ∀ b, decode (cut b) = decode b)
 (a : OwnedAccount) (k : A → RS B) :
 RS.bind (account a).data
   (fun b => RS.bind (RS.bind (RS.ofOption (decode b) .invalidAccountData)
      (fun x => RS.seq (RS.lift Spec.alloc) (RS.pure x))) k) =
 RS.bind a.data
   (fun b => RS.bind (RS.bind (RS.ofOption (decode b) .invalidAccountData)
      (fun x => RS.seq (RS.lift Spec.alloc) (RS.pure x))) k) := by
 cases hb : a.bytes with
 | ok b => simp only [account,OwnedAccount.data,hb,Except.map,RS.ofCloned_ok,RS.bind_pure,law]
 | error e => simp only [account,OwnedAccount.data,hb,Except.map]

theorem lane {B : Type} (a : OwnedAccount) (k : LaneState → RS B) :
 RS.bind (account a).data
   (fun b => RS.bind (Spec.call TX2_217.Domain TX2_217.Ref b) k) =
 RS.bind a.data
   (fun b => RS.bind (Spec.call TX2_217.Domain TX2_217.Ref b) k) := by
 cases hb : a.bytes with
 | ok b =>
   simp only [account,OwnedAccount.data,hb,Except.map,RS.ofCloned_ok,RS.bind_pure]
   have same : Spec.call TX2_217.Domain TX2_217.Ref (cut b) =
       Spec.call TX2_217.Domain TX2_217.Ref b := by
     funext env obs
     change (True ∧ TX2_217.Ref (cut b) env obs) = (True ∧ TX2_217.Ref b env obs)
     rw [NMX_R4_ByteCut.lane]
   rw [same]
 | error e => simp only [account,OwnedAccount.data,hb,Except.map]
#print axioms boxed
#print axioms lane
end NMX_R4_ReadDecode
end
