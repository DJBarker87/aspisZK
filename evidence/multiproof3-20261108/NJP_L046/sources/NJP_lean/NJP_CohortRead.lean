import NJP_CohortWrite
import NJA_Reads

set_option autoImplicit false
noncomputable section
namespace NJP_CohortRead
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef

theorem index (s : reference.Scratch) (i : Usize) (bound : i.val<16) :
 NJP_RowModel.index (raw s) i.val=(s.idx.val[i.val]!).val := by
 have size : s.idx.val.length=16 := s.idx.property
 simp only [NJP_RowModel.index,if_pos bound,raw,decodeIndices,getElem!_pos _ _ (by omega)]

theorem value (s : reference.Scratch) (i : Usize) (bound : i.val<16) :
 NJP_RowModel.value (raw s) i.val=decode (s.val.val[i.val]!) := by
 have size : s.val.val.length=16 := s.val.property
 simp only [NJP_RowModel.value,if_pos bound,raw,decodeValues,getElem!_pos _ _ (by omega)]

theorem xor_one (x : U32) : (x ^^^ 1#u32).val=Nat.xor x.val 1 := by
 scalar_tac

theorem parity (x : U32) : (x &&& 1#u32).val=x.val%2 := by
 scalar_tac

theorem occupied_address (s : reference.Scratch) (i next : Usize)
    (bound : i.val<16) (next_bound : next.val<16) (step : next.val=i.val+1) :
 NJP_RequestTransport.address (NJP_RowModel.occupiedRequest (raw s) i.val)=
 AspisR1.MultiproofConePhysicalDigest.parts (s.val.val[i.val]!) (s.val.val[next.val]!) := by
 unfold NJP_RequestTransport.address NJP_RowModel.occupiedRequest
 rw [value s i bound,←step,value s next next_bound]
 simp only [encode_decode]

#print index
#print axioms index
#print value
#print axioms value
#print xor_one
#print axioms xor_one
#print parity
#print axioms parity
#print occupied_address
#print axioms occupied_address
end NJP_CohortRead
end
