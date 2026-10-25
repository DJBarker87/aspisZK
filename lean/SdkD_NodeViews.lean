import SdkD_RootBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_NodeViews
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft

/-- Physical node slices are computed from this proof's own bytes. -/
def nodes (proof : Slice U8) (batch kind : Nat) : Slice U8 :=
  ⟨(proof.val.drop (slotStart (3*batch+kind))).take (32*capacity (3*batch+kind)),by
    have room := proof.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem views (proof : Slice U8) (parsed : Parsed) (wire : parsed.wire = bytesOf proof.val)
    (batch kind : Nat) :
    bytesOf (nodes proof batch kind).val = slice parsed.wire
      (slotStart (3*batch+kind)) (32*capacity (3*batch+kind)) := by
  simp only [nodes,bytesOf,slice,List.map_take,List.map_drop,wire]

#print axioms views
end AspisR1.SdkD_NodeViews
end
