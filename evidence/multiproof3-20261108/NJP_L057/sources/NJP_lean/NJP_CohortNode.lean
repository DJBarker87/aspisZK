import NJP_CohortSupplied

set_option autoImplicit false
noncomputable section
namespace NJP_CohortNode
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.MultiproofConePhysicalProgram

theorem unpaired (s : reference.Scratch) (physical : Slice U8) (i ni w : Usize)
    (bound : i.val<s.n.val) (size : s.n.val≤16)
    (addition : i+1#usize=ok ni) (next_value : ni.val=i.val+1)
    (single : ¬NJP_RowModel.paired (raw s) i.val) :
 node s physical i w=NJP_CohortSupplied.supplied s physical ni
   (s.idx.val[i.val]!) (s.val.val[i.val]!) w := by
 have ib : i.val<16 := by omega
 unfold node
 rw [NJP_CohortOccupied.read s.idx i ib,NJP_CohortOccupied.read s.val i ib,addition]
 simp only [checked]
 by_cases live : ni<s.n
 · rw [if_pos live]
   have nb : ni.val<16 := by change ni.val<s.n.val at live;omega
   rw [NJP_CohortOccupied.read s.idx ni nb]
   simp only [checked]
   have different : ¬s.idx.val[ni.val]! = s.idx.val[i.val]! ^^^ 1#u32 := by
     intro same
     apply single
     constructor
     · change ni.val<s.n.val at live;omega
     · rw [←next_value,NJP_CohortRead.index s ni nb,NJP_CohortRead.index s i ib]
       have scalar := congrArg UScalar.val same
       rw [NJP_CohortRead.xor_one] at scalar
       exact scalar
   rw [if_neg different]
   rfl
 · rw [if_neg live]
   rfl

theorem observation (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (physical : Slice U8) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w)
    (active : i.val<s.n.val) :
 let typed := eval H (node s physical i w)
 (typed.1,mapResult projectRow typed.2)=
 eval H (NJP_RequestTransport.transport
   (NJP_RowModel.node (fun n => physical.val[n]!) physical.val.length (raw s) i.val w.val)) := by
 by_cases both : NJP_RowModel.paired (raw s) i.val
 · exact NJP_CohortOccupied.occupied H s physical i w domain active both
 · have ib : i.val<16 := by have := domain.2.1;omega
   have wb : w.val<16 := by have := domain.2.2.2.1;omega
   obtain ⟨ni,addition,next_value⟩ := NJP_CheckedWords.add_one i ib
   dsimp only
   rw [unpaired s physical i ni w active domain.2.1 addition next_value both]
   by_cases enough : s.«at».val+32≤physical.val.length
   · rw [NJP_CohortSupplied.available H s physical i ni w next_value ib wb enough]
     rw [NJP_RequestTransport.observation,NJP_RowModel.sibling_observation _ _ _ _ _ _ active both enough]
     simp only [List.map_cons,List.map_nil,NJP_RequestTransport.hash,encode_decode]
     rfl
   · have short : physical.val.length<s.«at».val+32 := by omega
     rw [NJP_CohortSupplied.missing H s physical ni _ _ w domain.2.2.2.2 short]
     rw [NJP_RequestTransport.observation,NJP_RowModel.missing_observation _ _ _ _ _ _ active both short]
     rfl

#print unpaired
#print axioms unpaired
#print observation
#print axioms observation
end NJP_CohortNode
end
