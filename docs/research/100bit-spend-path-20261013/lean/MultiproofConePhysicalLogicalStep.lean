import MultiproofConePhysicalViews
import MultiproofConePhysicalNode

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConePhysicalLogicalStep
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalDigest MultiproofConePhysicalNode
open MultiproofConePhysicalLive MultiproofConePhysicalViews MultiproofConePhysicalAddress
open MultiproofConeLiveReference MultiproofConeOrderedLevel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem pair_nat (s : reference.Scratch) (i : Usize) :
    SourcePair s i ↔ i.val+1<s.n.val ∧ s.idx.val[i.val+1]!.val=s.idx.val[i.val]!.val^^^1 := by
  unfold SourcePair
  constructor
  · rintro ⟨more,eq⟩
    refine ⟨more,?_⟩
    scalar_tac
  · rintro ⟨more,eq⟩
    refine ⟨more,?_⟩
    apply UScalar.eq_of_val_eq
    scalar_tac

theorem source_guard (s : reference.Scratch) (i : Usize) :
    (match live s (i.val+1) (s.n.val-(i.val+1)) with
      | (j,_)::_ => decide (j=s.idx.val[i.val]!.val^^^1) | [] => false)=decide (SourcePair s i) := by
  by_cases more : i.val+1<s.n.val
  · have len : s.n.val-(i.val+1)=(s.n.val-(i.val+2))+1 := by omega
    rw [len,live_cons]
    simp only [decodeEntry,cell]
    have eq : SourcePair s i ↔ s.idx.val[i.val+1]!.val=s.idx.val[i.val]!.val^^^1 := by
      rw [pair_nat];simp only [more,true_and]
    exact decide_eq_decide.mpr eq.symm
  · have len : s.n.val-(i.val+1)=0 := by omega
    rw [len,live_empty]
    have np : ¬SourcePair s i := fun h => more h.1
    simp only [np,decide_false]

set_option backward.isDefEq.respectTransparency false in
/-- Exact source-shaped logical one-node unfolding from physical child reads,
including the supplied sibling bytes and cursor rebasing. -/
theorem logical_step (fuel : Nat) (physical : Slice U8) (s : reference.Scratch) (i ni cursor : Usize)
    (left right : MultiproofConePhysicalProgram.Digest) (active : i.val<s.n.val)
    (input : Input physical s i left right ni cursor) :
    sourceLevel (fuel+1) (live s i.val (s.n.val-i.val)) (remaining physical s.«at») =
      .ask (flatten (parts left right)) fun answer =>
        bind (sourceLevel fuel (live s ni.val (s.n.val-ni.val)) (remaining physical cursor)) fun out =>
          .done (out.map fun x => ((s.idx.val[i.val]!.val/2,answer)::x.1,x.2)) := by
  have len : s.n.val-i.val=(s.n.val-(i.val+1))+1 := by omega
  rw [len,live_cons]
  by_cases more : i.val+1<s.n.val
  · have len2 : s.n.val-(i.val+1)=(s.n.val-(i.val+2))+1 := by omega
    rw [len2,live_cons]
    simp only [decodeEntry,cell,sourceLevel,decide_eq_true_eq]
    by_cases pair : SourcePair s i
    · have natPair := (pair_nat s i).mp pair
      simp only [natPair.2,if_true]
      rw [Input,if_pos pair] at input
      obtain ⟨rfl,rfl,nextVal,rfl⟩ := input
      rw [nextVal,parent_address]
      rfl
    · have notNat : ¬s.idx.val[i.val+1]!.val=s.idx.val[i.val]!.val^^^1 :=
        fun h => pair ((pair_nat s i).mpr ⟨more,h⟩)
      simp only [notNat,if_false]
      have noPair : ¬SourcePair s i := by first | exact pair | exact fun h => more h.1
      rw [Input,if_neg noPair] at input
      obtain ⟨sibling,bytes,order,nextVal,cursorVal⟩ := input
      rw [sibling_decode physical s.«at» sibling bytes]
      have rest : remaining physical cursor=(remaining physical s.«at»).drop 32 :=
        (remaining_step physical s.«at» cursor cursorVal).symm
      rw [nextVal,rest,parent_address]
      by_cases even : s.idx.val[i.val]!.val%2=0
      · simp only [even,if_true] at order ⊢
        obtain ⟨rfl,rfl⟩ := order
        simp only [len2,live_cons,live_empty,decodeEntry,cell]
      · simp only [even,if_false] at order ⊢
        obtain ⟨rfl,rfl⟩ := order
        simp only [len2,live_cons,live_empty,decodeEntry,cell]
  · have len2 : s.n.val-(i.val+1)=0 := by omega
    rw [len2,live_empty]
    simp only [decodeEntry,cell,sourceLevel,Bool.false_eq_true,if_false]
    have noPair : ¬SourcePair s i := by first | exact pair | exact fun h => more h.1
    rw [Input,if_neg noPair] at input
    obtain ⟨sibling,bytes,order,nextVal,cursorVal⟩ := input
    rw [sibling_decode physical s.«at» sibling bytes]
    have rest : remaining physical cursor=(remaining physical s.«at»).drop 32 :=
      (remaining_step physical s.«at» cursor cursorVal).symm
    rw [nextVal,rest,parent_address]
    by_cases even : s.idx.val[i.val]!.val%2=0
    · simp only [even,if_true] at order ⊢
      obtain ⟨rfl,rfl⟩ := order
      simp only [len2,live_cons,live_empty,decodeEntry,cell]
    · simp only [even,if_false] at order ⊢
      obtain ⟨rfl,rfl⟩ := order
      simp only [len2,live_cons,live_empty,decodeEntry,cell]

#print axioms pair_nat
#print axioms source_guard
#print axioms logical_step
end AspisR1.MultiproofConePhysicalLogicalStep
end
