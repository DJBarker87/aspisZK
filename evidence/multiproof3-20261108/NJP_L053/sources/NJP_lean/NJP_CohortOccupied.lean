import NJP_CohortRead
import NJP_WindowCarrier
import NJP_RowInvariant

set_option autoImplicit false
noncomputable section
namespace NJP_CohortOccupied
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

-- Generic Std read reused at each exact caller place; no producer premise.
theorem read {α : Type} [Inhabited α] (a : Array α 16#usize) (i : Usize) (bound : i.val<16) :
 Array.index_usize a i=ok (a.val[i.val]!) := by
 have size : a.val.length=16 := a.property
 rw [NJA_Reads.index_ok a i (by change i.val<16;exact bound),getElem!_pos a.val i.val (by omega)]

theorem occupied (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (physical : Slice U8) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w)
    (active : i.val<s.n.val) (both : NJP_RowModel.paired (raw s) i.val) :
 let typed := eval H (AspisR1.MultiproofConePhysicalProgram.node s physical i w)
 (typed.1,mapResult projectRow typed.2)=
 eval H (NJP_RequestTransport.transport
   (NJP_RowModel.node (fun n => physical.val[n]!) physical.val.length (raw s) i.val w.val)) := by
 obtain ⟨positive,size,readBound,writeBound,cursorBound⟩ := domain
 have ib : i.val<16 := by omega
 have wb : w.val<16 := by omega
 obtain ⟨next,addition,next_value⟩ := NJP_CheckedWords.add_one i ib
 have nextNat : i.val+1<s.n.val := both.1
 have nb : next.val<16 := by omega
 have next_active : next<s.n := by change next.val<s.n.val;omega
 have equality : s.idx.val[next.val]! = s.idx.val[i.val]! ^^^ 1#u32 := by
   apply UScalar.eq_of_val_eq
   rw [NJP_CohortRead.xor_one]
   have values := both.2
   rw [←next_value,NJP_CohortRead.index s next nb,NJP_CohortRead.index s i ib] at values
   exact values
 obtain ⟨next2,addition2,next2_value⟩ := NJP_CheckedWords.add_two i (by omega)
 have address := NJP_CohortRead.occupied_address s i next ib nb next_value
 dsimp only
 unfold AspisR1.MultiproofConePhysicalProgram.node
 rw [read s.idx i ib,read s.val i ib,addition]
 simp only [AspisR1.MultiproofConePhysicalProgram.checked]
 rw [if_pos next_active,read s.idx next nb]
 simp only [AspisR1.MultiproofConePhysicalProgram.checked]
 rw [if_pos equality,read s.val next nb,addition2]
 simp only [AspisR1.MultiproofConePhysicalProgram.checked]
 rw [NJP_CohortWrite.writer H s _ _ next2 s.«at» _ i w wb (NJP_CohortRead.index s i ib).symm]
 rw [NJP_RequestTransport.observation]
 rw [NJP_RowModel.occupied_observation _ _ _ _ _ _ active both]
 simp only [List.map_cons,List.map_nil,NJP_RequestTransport.hash,encode_decode,next2_value]
 rw [address]
 rfl

#print read
#print axioms read
#print occupied
#print axioms occupied
end NJP_CohortOccupied
end
