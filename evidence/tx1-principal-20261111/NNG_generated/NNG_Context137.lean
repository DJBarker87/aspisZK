import NNG_FinishAdapter137
import NNG_BeginSource137
import NNG_Parse137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Context137
open Aeneas Aeneas.Std Result NMP_prepare
abbrev Public := NMP_Emitted.Public
abbrev Observer := NMP_Emitted.Observer
abbrev Output (H : Type) := NMP_Emitted.SemanticOut H
structure Calls where
  begin_ : ∀ {H : Type},aspis_core.digest.Digest32 H → r1_wire.Prefix → r1_wire.SemanticTranscript H →
    Result (core.result.Result aspis_core.state_only_prefix.r0.Challenges r1_wire.Error × r1_wire.SemanticTranscript H)
  parse : Slice U8 → Result (core.result.Result r1_wire.Prefix r1_wire.Error)
  finish : ∀ {H : Type},aspis_core.digest.Digest32 H → Public → r1_wire.Prefix → r1_wire.SemanticTranscript H →
    aspis_core.state_only_prefix.r0.Challenges → Observer → Result (Output H)
  mark : Observer → U8 → Result Unit
  publicTranscript : ∀ {H : Type},aspis_core.digest.Digest32 H → Public → H → Array U8 32#usize →
    Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
structure Parent (H : Type) where
  digest : aspis_core.digest.Digest32 H
  publicValue : Public
  bytes : Slice U8
  hash : H
  observer : Observer

def calls (env : RSL.Env) : Calls :=
  ⟨NMP_Install150.begin_,NMP_Install138.parse,NNG_FinishAdapter137.call env,(fun _ _=>.ok ()),NMP_Install131.publicTranscript⟩
def observer (obs : RSL.Observer) : Observer := obs.map (fun _=>fun _=>.ok ())
def input (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env) : Parent Unit :=
  ⟨NNG_PublicSource137.digest env,NMP_Transport.fromT9 a.public_,NNG_Data137.bytes a.bytes,(),observer obs⟩
def emitted {H : Type} (c : Calls) (s : Parent H) : Result (Output H) :=
  NMP_prepare.r1_semantic.verify_observed c.begin_ c.parse c.finish c.mark c.publicTranscript
    s.digest s.publicValue s.bytes s.hash s.observer
end AspisR1.NNG_Context137
