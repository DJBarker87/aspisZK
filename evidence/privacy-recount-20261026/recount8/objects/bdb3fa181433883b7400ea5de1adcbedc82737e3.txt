import R1Z.PV_RunJoin_RoundRecord43
import R1Z.PV_RunJoin_RecordSlice43
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RoundStream43
open Aeneas Aeneas.Std PV_RunJoin_RoundRecord43 PV_RunJoin_ByteExtension43

theorem added_length {a b : List U8} (h : Added a b) : b.length=a.length+901 := by
  obtain ⟨header,body,hlen,blen,hz,hb⟩ := h
  rw [hb,List.length_append,List.length_append,hlen,blen]

inductive Stream : List U8 → Nat → List U8 → Prop where
  | nil (bytes : List U8) : Stream bytes 0 bytes
  | cons {before middle after : List U8} {n : Nat} (head : Added before middle)
      (tail : Stream middle n after) : Stream before (n+1) after

theorem extension {before after : List U8} {n : Nat} (h : Stream before n after) :
    Ext before after (901*n) := by
  induction h with
  | nil bytes => exact PV_RunJoin_ByteExtension43.refl bytes
  | @cons before middle after n head tail ih =>
    obtain ⟨header,body,hlen,blen,hz,hb⟩ := head
    have one : Ext before middle 901 :=
      ⟨header++body,by rw [List.length_append,hlen,blen],by rw [hb,List.append_assoc]⟩
    have h := PV_RunJoin_ByteExtension43.trans one ih
    convert h using 1 <;> omega

theorem length {before after : List U8} {n : Nat} (h : Stream before n after) :
    after.length=before.length+901*n := PV_RunJoin_ByteExtension43.length (extension h)

theorem canonical {before after : List U8} {n : Nat} (h : Stream before n after)
    (k : Nat) (bound : k<n) :
    PV_RunJoin_HighDomain40.HighZero ((after.drop (before.length+901*k+5)).take 896) := by
  induction h generalizing k with
  | nil bytes => omega
  | @cons before middle after n head tail ih =>
    cases k with
    | zero =>
      obtain ⟨header,body,hlen,blen,hz,hb⟩ := head
      obtain ⟨suffix,sl,hs⟩ := extension tail
      have slice := PV_RunJoin_RecordSlice43.payload before header body suffix hlen
      rw [hs,hb]
      simp only [Nat.mul_zero,Nat.add_zero]
      rw [←blen,PV_RunJoin_RecordSlice43.payload before header body suffix hlen]
      exact hz
    | succ k =>
      have ml := added_length head
      have off : before.length+901*(k+1)+5=middle.length+901*k+5 := by omega
      rw [off]
      exact ih k (by omega)
#print axioms added_length
#print axioms extension
#print axioms length
#print axioms canonical
end R1Z.PV_RunJoin_RoundStream43
