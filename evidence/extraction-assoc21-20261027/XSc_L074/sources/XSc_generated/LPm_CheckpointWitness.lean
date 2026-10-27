import LPm_CheckpointDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPm_CheckpointWitness
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytesBlocks CheckpointBytesBody
open LPm_CheckpointTrace

theorem append_trace (xs : List (List U8)) (buf : List U8) :
    Appends xs buf (buf ++ xs.flatten) := by
  induction xs generalizing buf with
  | nil => simpa only [List.flatten_nil,List.append_nil] using Appends.done buf
  | cons b xs ih =>
    have t := Appends.step b xs buf (buf++b) ((buf++b)++xs.flatten) rfl (ih (buf++b))
    simpa only [List.flatten_cons,List.append_assoc] using t

/-- Local trace consistency for EVERY domain input and EVERY three replies.
The linked prefix, actual weights and checksum append are constructed, never
postulated as a whole-output equality. This is a model consistency witness;
the native gates/source association supply the physical execution instance. -/
theorem all_replies (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)
    (hp hu hc : Digest) : ∃ body out, Nonempty (Trace p a size qb hp hu hc body out) := by
  let pre := ((prefixBlocks p a size qb hp hu).map (List.map u8)).flatten
  have plen : pre.length = 712 := by
    dsimp only [pre]
    rw [← List.map_flatten,List.length_map]
    exact LPm_CheckpointDomains.prefix_length p a size qb canonical next hp hu
  let bs := LPi_SerializationFold.fold pre a.weights.val
  have blen : bs.length = 1736 := by
    dsimp only [bs]
    rw [LPi_SerializationFold.length,plen,size]
  let body : Slice U8 := ⟨bs,by rw [blen]; scalar_tac⟩
  let out : Slice U8 := ⟨bs++hc.val,by
    rw [List.length_append,blen,hc.property]; scalar_tac⟩
  refine ⟨body,out,⟨⟨pre,?_,LPm_WeightLoop.exists_trace a.weights.val pre,rfl⟩⟩⟩
  simpa only [List.nil_append] using
    append_trace ((prefixBlocks p a size qb hp hu).map (List.map u8)) []

#print axioms append_trace
#print axioms all_replies
end AspisR1.LPm_CheckpointWitness
end
