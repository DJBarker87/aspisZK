import R1Z.PV_Inv_BankPattern
set_option autoImplicit false
namespace R1Z.PV_Inv_TaggedBank
open R0P PV_Inv_BankSource PV_Inv_BankPattern
variable {K : Type} [Field K]

def tagged (banks : Banks K) (tag : Nat) (raw : Tuple K) : K × (Fin 16 → K) :=
  ((tag : K),value banks raw)

theorem source_equation (banks : Banks K) (t : Trace K) (join : BankJoin banks t)
    (tag : Nat) (e : CopyEndpoint) (raw : Tuple K) (descriptor_join : raw = descriptor e) :
    tagged banks tag raw = copyEndpointTuple t tag e := by
  subst raw
  exact congrArg (fun limbs => ((tag : K),limbs)) (PV_Inv_BankPattern.tuple banks t join e)

#print axioms source_equation
end R1Z.PV_Inv_TaggedBank
