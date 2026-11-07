import NMX_SourceModel
set_option autoImplicit false
noncomputable section
namespace NMX_FrameLaws
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- Complete external frame, not just account-byte equality. This is a model
lemma; the canonical native child packets must justify that interpretation. -/
theorem returned_frame {W E A : Type} (before post : W) (events es : List E)
 (r : Result (core.result.Result A PE))
 (reply : core.result.Result A PE)
 (h : returned before events r = End.returned reply post es) : post = before := by
 cases r with
 | fail e => cases h
 | div => cases h
 | ok value => cases h; rfl

theorem source_frame {W B : Type} (ops : AdapterRw.Ops) (owners : Owners)
 (cmd : Command B) (before post : W) (reply : core.result.Result B PE)
 (events : List NLM_Auth233.Event)
 (h : source ops owners cmd before = End.returned reply post events) : post = before := by
 cases cmd <;> first
 | exact returned_frame before post _ events _ reply h
 | cases h; rfl
#print axioms returned_frame
#print axioms source_frame
end NMX_FrameLaws
end
