import R1Z.PV_RDEA_NameBytes
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_NameFill
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_AppendNoGrowth
open PV_RDEA_NameBytes PV_RDEA_ReservationName

def afterCopy {S F : Type} (b : Buffer U8) (tail : List U8) (w : World S F) : World S F :=
  {w with memory:=PV_RDB1_Append.writeTail b.address b.values.length tail w.memory}

/-- Same order as reservation_name: one high-digit append, one low-digit
append, recurse; one final suffix append. -/
def fill {S F : Type} (step : Request → S → Option Nat × S) (shape : Shape) :
    List (Fin 256) → Buffer U8 → World S F → Outcome (Buffer U8) S F
  | [],b,w => PV_RDEA_AppendExecution.append step shape b PV_RDEA_NameBytes.suffix w
  | head::rest,b,w =>
    PV_RDEA_StatefulPath.bind
      (PV_RDEA_AppendExecution.append step shape b [digitByte (high head)] w) fun b w =>
    PV_RDEA_StatefulPath.bind
      (PV_RDEA_AppendExecution.append step shape b [digitByte (low head)] w) fun b w =>
    fill step shape rest b w

theorem complete {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (digest : List (Fin 256)) (b : Buffer U8) (w : World S F)
    (fits : b.values.length+2*digest.length+5≤b.capacity) :
    ∃ out after, fill step shape digest b w=(.ok out,after) ∧
      out.capacity=b.capacity ∧ out.values=b.values++bytes digest ∧
      out.address=b.address ∧ after.allocator=w.allocator ∧
      after.history=w.history ∧ after.frame=w.frame := by
  induction digest generalizing b w with
  | nil =>
    have hf : b.values.length+PV_RDEA_NameBytes.suffix.length≤b.capacity := by
      simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero,PV_RDEA_NameBytes.suffix,List.length_cons] using fits
    refine ⟨appended b PV_RDEA_NameBytes.suffix hf,afterCopy b PV_RDEA_NameBytes.suffix w,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
    exact PV_RDEA_AppendNoGrowth.complete step shape b _ w hf
  | cons head rest ih =>
    simp only [List.length_cons] at fits
    let hi := [digitByte (high head)]
    let lo := [digitByte (low head)]
    have hf : b.values.length+hi.length≤b.capacity := by dsimp [hi]; omega
    let b1 := appended b hi hf
    let w1 := afterCopy b hi w
    have hl : b1.values.length+lo.length≤b1.capacity := by
      simp only [b1,appended,List.length_append,hi,lo,List.length_cons,List.length_nil]
      omega
    let b2 := appended b1 lo hl
    let w2 := afterCopy b1 lo w1
    have remaining : b2.values.length+2*rest.length+5≤b2.capacity := by
      simp only [b2,b1,appended,List.length_append,hi,lo,List.length_cons,List.length_nil]
      omega
    obtain ⟨out,after,run,hcap,hval,haddr,halloc,hhist,hframe⟩ := ih b2 w2 remaining
    refine ⟨out,after,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [fill,PV_RDEA_AppendNoGrowth.complete step shape b hi w hf]
      simp only [PV_RDEA_StatefulPath.bind]
      change PV_RDEA_StatefulPath.bind (PV_RDEA_AppendExecution.append step shape b1 lo w1) (fun b w => fill step shape rest b w) = _
      rw [PV_RDEA_AppendNoGrowth.complete step shape b1 lo w1 hl]
      simp only [PV_RDEA_StatefulPath.bind]
      exact run
    · simpa only [b2,b1,appended] using hcap
    · change out.values=b.values++(hi++lo++bytes rest)
      simpa only [b2,b1,appended,List.append_assoc] using hval
    · simpa only [b2,b1,appended] using haddr
    · simpa only [w2,w1,afterCopy] using halloc
    · simpa only [w2,w1,afterCopy] using hhist
    · simpa only [w2,w1,afterCopy] using hframe

#print axioms complete
end R1Z.PV_RDEA_NameFill
