import NLI_Suffix_mark4
import NLI_MonadNotation
import NLI_Window_terminalGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_terminalGuard {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (masked : Q) : Code (Out H) := do
 let reject ← core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running masked
 if reject then pure (.Err r1_wire.Error.Terminal) else suffix_mark4 i (alpha) (transcript) (claims) (extra)
theorem terminalGuard {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (masked : Q) :
 run (fold 16 {input:=i,next:=.terminalGuard,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, masked:=some masked}}) = run (suffix_terminalGuard i (running) (alpha) (transcript) (claims) (extra) (masked)) := by
 rw [NLI_Window.terminalGuard_head 15]
 unfold NLI_Window.window_terminalGuard suffix_terminalGuard
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro reject
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases reject with
 | false => exact mark4 i ({l with running:=some running, masked:=some masked}) (alpha) (transcript) (claims) (extra)
 | true => rfl
#print axioms terminalGuard
end AspisR1.NLI_Source
end
