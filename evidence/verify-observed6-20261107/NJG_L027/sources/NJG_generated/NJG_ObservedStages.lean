import NJG_Results
set_option autoImplicit false
namespace AspisR1.NJG_ObservedStages
open Aeneas Aeneas.Std Result NIX_EmittedTypes NIX_ObservedBody

def rustBind {A B E : Type} (r : Result (core.result.Result A E))
 (next : A→Result (core.result.Result B E)) : Result (core.result.Result B E) := do
 let reply←r
 match reply with
 | .Ok value=>next value
 | .Err error=>ok (.Err error)

def stage {H : Type} (B : Boundaries H) (D : aspis_core.digest.Digest32 H)
 (pubdata : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) : Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error) :=
 rustBind (B.parse bytes) fun pre=>
 rustBind (B.pubdataTranscript D pubdata hash pre.c1_root) fun transcript=>do
 let (reply,post)←B.begin D pre transcript
 match reply with
 | .Err error=>ok (.Err error)
 | .Ok challenge=>B.finish D pubdata pre post challenge none

/-- Explicit source-order segmentation of the sole NIX root emission.
All four children remain actual boundary calls; no callee clause is a premise.
This is not yet the adopted-cohort/op9 transport. -/
theorem source {H : Type} (B : Boundaries H) (D : aspis_core.digest.Digest32 H)
 (pubdata : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) : emitted B D pubdata bytes hash none=stage B D pubdata bytes hash := by
 unfold emitted stage rustBind
 cases hp:B.parse bytes with
 | fail error=>rfl
 | div=>rfl
 | ok reply=>cases reply with
   | Err error=>rfl
   | Ok pre=>
     cases ht:B.pubdataTranscript D pubdata hash pre.c1_root with
     | fail error=>rfl
     | div=>rfl
     | ok reply=>cases reply with
       | Err error=>rfl
       | Ok transcript=>
         cases hb:B.begin D pre transcript with
         | fail error=>rfl
         | div=>rfl
         | ok pair=>rcases pair with ⟨reply,post⟩;cases reply <;> rfl

theorem parse_rejection {H : Type} (B : Boundaries H) (D : aspis_core.digest.Digest32 H)
 (pubdata : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (error : r1_wire.Error)
 (rejected : B.parse bytes=ok (.Err error)) : emitted B D pubdata bytes hash none=ok (.Err error) := by
 rw [source]
 simp only [stage,rustBind,rejected,bind_tc_ok]

#print axioms source
#print axioms parse_rejection
end AspisR1.NJG_ObservedStages
