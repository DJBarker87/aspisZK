import LIBB_FlattenBytes
import NNC_DigestTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_C04LogGraph
open Aeneas Aeneas.Std AspisR1
/-- A value-level C04 query shape, not a native execution relation. -/
def Canonical : SdkC_Source.Query → Prop
 | ⟨parts,reply⟩ => ∃ out, reply = .ok out ∧
   LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
    (AspisV8R19.SqueezeOracleBridge.flatten parts)) = NNC_ResumeEvents.parts parts

def render (history : NLL.History) : List RSL.Event :=
 history.map (fun e => .digest (LIBB_C04Partition.partition (LIBB_ProtocolBytes.host e.1))
   (NNC_ResumeEvents.digest (AspisV8R19.SqueezeOracleBridge.encodeState e.2)))

theorem append (a b : NLL.History) : render (a ++ b) = render a ++ render b := List.map_append

theorem one (q : SdkC_Source.Query) (shape : Canonical q) :
 NNC_DigestTrace.render [.attempted q] = render (SdkC_Source.readLog [q]) := by
 cases q with
 | mk parts reply =>
   obtain ⟨out,rfl,partition⟩ := shape
   change [RSL.Event.digest (NNC_ResumeEvents.parts parts) (NNC_ResumeEvents.digest out)] =
     [RSL.Event.digest
       (LIBB_C04Partition.partition (LIBB_ProtocolBytes.host
         (AspisV8R19.SqueezeOracleBridge.flatten parts)))
       (NNC_ResumeEvents.digest (AspisV8R19.SqueezeOracleBridge.encodeState
         (AspisV8R19.SqueezeOracleBridge.decodeState out)))]
   rw [partition,AspisV8R19.SqueezeOracleBridge.array_roundtrip]

theorem log (queries : SdkC_Source.Log) (shape : ∀ q ∈ queries, Canonical q) :
 NNC_DigestTrace.render (queries.map NNC_DigestTrace.Step.attempted) =
 render (SdkC_Source.readLog queries) := by
 induction queries with
 | nil => rfl
 | cons q rest ih =>
   change NNC_DigestTrace.render ([.attempted q] ++ rest.map NNC_DigestTrace.Step.attempted) =
    render (SdkC_Source.readLog ([q] ++ rest))
   rw [NNC_DigestTrace.render_append,NNC_C04Events.read_append,append,
     one q (shape q (by simp)),ih (fun x hx => shape x (List.mem_cons_of_mem q hx))]

/-- Node byte/reply transport is exact for every arbitrary request pair. -/
theorem nodes (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest)) :
 ∀ q ∈ NNC_C04Events.nodes queries, Canonical q := by
 intro q member
 obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
 exact ⟨NJP_DigestCarrier.encode e.2,rfl,LIBB_FlattenBytes.node _ _⟩
#print axioms append
#print axioms one
#print axioms log
#print axioms nodes
end LIBB_C04LogGraph
end
