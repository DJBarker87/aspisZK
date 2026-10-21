import MultiproofConePhysicalNode
import MultiproofConePhysicalTransport
import MultiproofConeNodeWindow

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalPrelude
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalNode MultiproofConeLiveReference
open MultiproofConeNodeDomain MultiproofConeNodeWindow

/-- Checked full-array read with its exact byte/index value. -/
theorem array_read {α : Type} [Inhabited α] {size : Usize} (a : Array α size) (i : Usize)
    (bound : i.val<size.val) : Array.index_usize a i=ok a.val[i.val]! := by
  have len := a.property
  have gi := getElem!_pos a.val i.val (by omega)
  have spec : Array.index_usize a i ⦃ out => out=a.val[i.val]! ⦄ := by
    step* <;> simp_all
  obtain ⟨out,eq,val⟩ := WP.spec_imp_exists spec
  rw [eq,val]

theorem parity (index : U32) : index &&& 1#u32=0#u32 ↔ index.val%2=0 := by
  constructor <;> intro h <;> scalar_tac_preprocess <;> simp_all [Nat.and_one_is_mod]

/-- Shared supplied-sibling prelude, before the unique parent hash. -/
def supply (s : reference.Scratch) (physical : Slice U8) (index : U32) (value : Digest)
    (ni w : Usize) : Run reference.Row :=
  checked (Slice.len physical-s.«at») fun remaining =>
    if remaining<32#usize then .done (.ok (.Stop s)) else
    checked (s.«at»+32#usize) fun cursor =>
    checked (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      physical {start:=s.«at»,«end»:=cursor}) fun chunk =>
    checked (reference.read32 chunk) fun sibling =>
    if index &&& 1#u32=0#u32 then writer s value sibling ni cursor index w
    else writer s sibling value ni cursor index w

/-- Program-level prelude normalization, retaining either ordinary short
rejection or the exact single ask and checked post-hash continuation. -/
theorem supply_form (s : reference.Scratch) (physical : Slice U8) (i ni w : Usize)
    (domain : RowDomain physical s i w) (noPair : ¬SourcePair s i)
    (niVal : ni.val=i.val+1) :
    supply s physical s.idx.val[i.val]! s.val.val[i.val]! ni w = .done (.ok (.Stop s)) ∨
    ∃ left right cursor,
      Input physical s i left right ni cursor ∧
      supply s physical s.idx.val[i.val]! s.val.val[i.val]! ni w =
        writer s left right ni cursor s.idx.val[i.val]! w := by
  obtain ⟨remaining,sub,remPost⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x:=Slice.len physical) (y:=s.«at») (by have := domain.2.2.2.2;scalar_tac))
  have remVal : remaining.val=physical.val.length-s.«at».val := by simpa [Slice.len] using remPost.1
  unfold supply
  rw [sub,checked]
  by_cases short : remaining<32#usize
  · exact Or.inl (by rw [if_pos short])
  · have enough : s.«at».val+32≤physical.val.length := by
      have := domain.2.2.2.2
      have h : ¬remaining.val<32 := short
      omega
    obtain ⟨cursor,sibling,chunk,add,cursorVal,range,read,content⟩ := physical_read physical s.«at» enough
    rw [if_neg short,add,checked,range,checked,read,checked]
    apply Or.inr
    by_cases even : s.idx.val[i.val]! &&& 1#u32=0#u32
    · refine ⟨s.val.val[i.val]!,sibling,cursor,?_,by rw [if_pos even]⟩
      simp only [Input,noPair,if_false]
      refine ⟨sibling,content,?_,niVal,cursorVal⟩
      simp only [(parity _).mp even,if_true];constructor <;> trivial
    · refine ⟨sibling,s.val.val[i.val]!,cursor,?_,by rw [if_neg even]⟩
      simp only [Input,noPair,if_false]
      refine ⟨sibling,content,?_,niVal,cursorVal⟩
      rw [if_neg (fun h => even ((parity _).mpr h))];constructor <;> trivial

#print axioms array_read
#print axioms parity
#print axioms supply_form
end AspisR1.MultiproofConePhysicalPrelude
