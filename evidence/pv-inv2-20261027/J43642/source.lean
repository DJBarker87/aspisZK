import R1Z.PV_Inv_RegistryInput
set_option autoImplicit false
namespace R1Z.PV_Inv_BankCompression
open R0P PV_Inv_BankSource PV_Inv_BankPattern PV_Inv_TaggedBank PV_Inv_RegistryInput
variable {K : Type} [Field K]

def producer (banks : Banks K) (lambda : K) (l : SourceLink K) : K :=
  copyTupleValue lambda (tagged banks l.tag l.producer)
def consumer (banks : Banks K) (lambda : K) (l : SourceLink K) : K :=
  copyTupleValue lambda (tagged banks l.tag l.consumer)

theorem producer_equation (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda : K) (l : CopyLink) :
    producer banks lambda (ofModel l) = copyTupleValue lambda (copyEndpointTuple t l.tag l.producer) := by
  unfold producer
  rw [show tagged banks (ofModel l).tag (ofModel l).producer =
    copyEndpointTuple t l.tag l.producer from source_equation banks t join l.tag l.producer _ rfl]

theorem consumer_equation (banks : Banks K) (t : Trace K) (join : P_banks banks t)
    (lambda : K) (l : CopyLink) :
    consumer banks lambda (ofModel l) = copyTupleValue lambda (copyEndpointTuple t l.tag l.consumer) := by
  unfold consumer
  rw [show tagged banks (ofModel l).tag (ofModel l).consumer =
    copyEndpointTuple t l.tag l.consumer from source_equation banks t join l.tag l.consumer _ rfl]

#print axioms producer_equation
#print axioms consumer_equation
end R1Z.PV_Inv_BankCompression
