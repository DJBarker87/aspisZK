import JFw_RecordAt
import ExtractedPrefixTrace
set_option autoImplicit false
namespace AspisR1.JFw_Chain
open Aeneas Aeneas.Std Result
open AspisR1PrefixAggregateParser ExtractedPrefixTrace

inductive Checked : List U8 → List (Slice U8) → Prop where
  | nil : Checked [] []
  | cons {row tag : U8} {size : Usize} {frame payload : Slice U8}
      {rows : List U8} {frames : List (Slice U8)}
      (shape : AspisR1RecordParser.r1_wire.row_shape row = ok (some (tag,size)))
      (length : frame.length = 5+size.val)
      (accepted : r1_wire.parse_record row frame = ok (.Ok payload))
      (tail : Checked rows frames) : Checked (row::rows) (frame::frames)

theorem construct (bytes : Slice U8) (rows : List U8) (frames : List (Slice U8))
    (checked : Checked rows frames) (offset : Usize)
    (bound : offset.val ≤ bytes.length)
    (suffix : bytes.val.drop offset.val = (frames.map (fun f => f.val)).flatten) :
    ∃ finish, RecordChain bytes rows offset frames finish ∧ finish.val = bytes.length := by
  induction checked generalizing offset with
  | nil =>
    refine ⟨offset,.nil _,?_⟩
    have lengths := congrArg List.length suffix
    simp only [List.map_nil,List.flatten_nil,List.length_nil,List.length_drop] at lengths
    change offset.val = bytes.val.length
    change offset.val ≤ bytes.val.length at bound
    omega
  | @cons row tag size frame payload rows frames shape length accepted checked ih =>
    have tailSuffix : bytes.val.drop offset.val = frame.val ++ (frames.map (fun f => f.val)).flatten := by
      simpa only [List.map_cons,List.flatten_cons] using suffix
    have endBound : offset.val+frame.length ≤ bytes.length := by
      have lengths := congrArg List.length tailSuffix
      simp only [List.length_drop,List.length_append] at lengths
      change frame.val.length = 5+size.val at length
      change offset.val ≤ bytes.val.length at bound
      change offset.val+frame.val.length ≤ bytes.val.length
      omega
    let next : Usize := ⟨offset.val+frame.length,by have h := bytes.property;scalar_tac⟩
    have nextValue : next.val = offset.val+5+size.val := by change offset.val+frame.length=_;omega
    have raw : (bytes.val.drop offset.val).take (5+size.val) = frame.val := by
      rw [tailSuffix,←length]
      exact List.take_left
    have call := JFw_RecordAt.success bytes frame payload row tag size offset next shape nextValue endBound raw accepted
    have rest : bytes.val.drop next.val = (frames.map (fun f => f.val)).flatten := by
      change bytes.val.drop (offset.val+frame.length) = _
      rw [←List.drop_drop,tailSuffix]
      exact List.drop_left
    obtain ⟨finish,chain,last⟩ := ih next endBound rest
    exact ⟨finish,.cons call chain,last⟩

#print axioms construct
end AspisR1.JFw_Chain
