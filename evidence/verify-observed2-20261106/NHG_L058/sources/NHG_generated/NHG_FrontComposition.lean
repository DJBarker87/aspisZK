import NHG_PublicCarrier
import NHG_BeginFrame
import NHG_ProgramChain
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NHG_FrontComposition

theorem bind_congr {A B : Type} (a b : Code A) (k l : A→Code B)
 (head : run a=run b) (tail : ∀ x,run (k x)=run (l x)) :
 run (a>>=k)=run (b>>=l) := by
 rw [NGX_RunBind.bind_run,NGX_RunBind.bind_run,head]
 cases reply : (run b).2 with
 | fail e => simp only [NGX_RunBind.appendResult,reply]
 | div => simp only [NGX_RunBind.appendResult,reply]
 | ok x => simp only [NGX_RunBind.appendResult,reply];rw [tail x]

def collect {H : Type}
 (call : Code (core.result.Result r1_wire.Challenges r1_wire.Error×r1_wire.SemanticTranscript H)) :
 Code (core.result.Result (r1_wire.Challenges×r1_wire.SemanticTranscript H) r1_wire.Error) := do
 let (result,after)←call
 pure (match result with | .Err error=>.Err error | .Ok c=>.Ok (c,after))

def source {H : Type} (D : aspis_core.Digest32 H) (p : NHG_Serializer.Public)
 (hash : H) (pre : r1_wire.Prefix) :
 Code (core.result.Result (r1_wire.Challenges×r1_wire.SemanticTranscript H) r1_wire.Error) := do
 let created←S1SemanticCode.publicTranscript D p hash pre.c1_root
 match created with
 | .Err error=>pure (.Err error)
 | .Ok initial=>collect (S1SemanticCode.begin D pre initial)

def packets {H : Type} (D : aspis_core.Digest32 H) (p : NHG_Serializer.Public)
 (hash : H) (pre : r1_wire.Prefix) :
 Code (core.result.Result (r1_wire.Challenges×r1_wire.SemanticTranscript H) r1_wire.Error) := do
 let created←NHG_PublicTranscript.packetCode D p hash pre.c1_root
 match created with
 | .Err error=>pure (.Err error)
 | .Ok initial=>collect (NHG_BeginPackets.begin S1SemanticCode.semanticValidated D pre initial)

/-- SAME public input and Vec producer, then SAME created transcript. This is
an equality of the complete chronological log AND Result, for all outcomes. -/
theorem staged {H : Type} (D : aspis_core.Digest32 H) (p : NHG_Serializer.Public)
 (hash : H) (pre : r1_wire.Prefix) :
 run (source D p hash pre)=run (packets D p hash pre) := by
 unfold source packets
 apply bind_congr
 · exact NHG_PublicTranscript.code D p hash pre.c1_root
 · intro created
   cases created with
   | Err error => rfl
   | Ok initial => rw [NHG_Begin.source]

#print axioms bind_congr
#print axioms staged
end AspisR1.NHG_FrontComposition
