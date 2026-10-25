import T2R_Parser
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_Selected
open Aeneas Aeneas.Std Result MultiproofConeCanonical OraclePortCompactDraft

/-- Any selected canonical parser output, including the continuation's
shared authParsed, is the prefix returned by this exact source proof. -/
theorem identify (proof : Slice U8) (facts : T2R_Parser.Facts proof)
    (selected : Parsed) (parser : parse (bytesOf proof.val) = some selected) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) ∧
      semanticRows 27 0 (slice (bytesOf proof.val) 48 6983) =
        some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      selected = ⟨bytesOf proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩ := by
  obtain ⟨expanded,pre,source,rows,canonical⟩ := facts
  exact ⟨expanded,pre,source,rows,Option.some.inj (parser.symm.trans canonical)⟩

#print axioms identify
end AspisR1.T2R_Selected
end
