import R1Z.PV_RunJoin_RecordSlice43
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CanonicalRecord43
open Aeneas Aeneas.Std PV_RunJoin_ByteExtension43 PV_RunJoin_HighDomain40

def Piece (size : Nat) (before after : List U8) : Prop :=
  ∃ header body : List U8, header.length=5 ∧ body.length=size ∧
    HighZero body ∧ after=before++header++body

theorem extension {size : Nat} {before after : List U8} (h : Piece size before after) :
    Ext before after (5+size) := by
  obtain ⟨header,body,hlen,blen,hz,hb⟩ := h
  exact ⟨header++body,by rw [List.length_append,hlen,blen],by rw [hb,List.append_assoc]⟩

theorem length {size : Nat} {before after : List U8} (h : Piece size before after) :
    after.length=before.length+5+size := by
  have hl := PV_RunJoin_ByteExtension43.length (extension h)
  omega

theorem slot {size n : Nat} {before after final : List U8}
    (h : Piece size before after) (tail : Ext after final n) :
    HighZero ((final.drop (before.length+5)).take size) := by
  obtain ⟨header,body,hlen,blen,hz,hb⟩ := h
  obtain ⟨suffix,sl,hs⟩ := tail
  rw [hs,hb,←blen,PV_RunJoin_RecordSlice43.payload before header body suffix hlen]
  exact hz

theorem preserve {before final : List U8} {n at1 size : Nat}
    (tail : Ext before final n) (bound : at1+size≤before.length)
    (high : HighZero ((before.drop at1).take size)) :
    HighZero ((final.drop at1).take size) := by
  obtain ⟨suffix,sl,hs⟩ := tail
  rw [hs,PV_RunJoin_RecordSlice43.preserved before suffix at1 size bound]
  exact high
#print axioms extension
#print axioms length
#print axioms slot
#print axioms preserve
end R1Z.PV_RunJoin_CanonicalRecord43
