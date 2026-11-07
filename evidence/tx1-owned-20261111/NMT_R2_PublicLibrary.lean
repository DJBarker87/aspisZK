import NMT_R2_Spec345
import NMT_345PublicDomain
set_option autoImplicit false
noncomputable section
namespace NMT_R2_PublicLibrary
open RSL NMT_345
/-- Representation-only specialization of the canonical verifier interface.
The Public carrier and its own canonical-domain clause are those already
proved for the emitted CLOSED268/276 fields. Remaining fields are inherited
through the explicit public representation map, not weakened. -/
def withPublic (V : VLib) (encodePublic : Public → V.Public) : VLib :=
 {V with
  Public := Public
  publicDom := publicDomain
  finishInputDom := fun p => V.finishInputDom (encodePublic p)
  terminalQm31 :=
   {dom := fun x => V.terminalQm31.dom (encodePublic x.1,x.2)
    law := fun x => V.terminalQm31.law (encodePublic x.1,x.2)}
  publicTranscript :=
   {dom := fun x => V.publicTranscript.dom (encodePublic x.1,x.2)
    law := fun x => V.publicTranscript.law (encodePublic x.1,x.2)}}

def valid (s : Statement) : Bool :=
 match validateCall s with
 | .ok (.Ok ()) => true
 | _ => false

theorem valid_iff (s : Statement) : valid s = true ↔ validateCall s = .ok (.Ok ()) := by
 unfold valid
 cases h : validateCall s with
 | fail e => simp
 | div => simp
 | ok r => cases r <;> simp

/-- Unconditional CLOSED276 → CLOSED268 domain transport, SAME statement.
No publicDom assumption on stage1_owned's inputs. -/
theorem semantic_domain (s : Statement) (good : valid s = true) :
 publicDomain (semanticValue s) :=
 validated_public_domain s ((valid_iff s).mp good)
#print axioms valid_iff
#print axioms semantic_domain
end NMT_R2_PublicLibrary
end
