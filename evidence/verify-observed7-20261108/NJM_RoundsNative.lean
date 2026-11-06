import NJG_RoundsCompose
import NJG_RoundsCode
set_option autoImplicit false
namespace AspisR1.NJM_RoundsNative
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_NativeCuts

/-- One original driver site instantiated with the actual SAME carry and
child reply; all window observations describe one post. -/
theorem step (s : RoundsPre) (post : RoundOutput) (frame : Nat)
 (cuts : ∀ k z limb,roundsResult {s with count:=0} k z limb post frame) :
 post=s.reply ∧ frame=s.frame := by
 refine ⟨NJG_RoundsCompose.complete {s with count:=0} post frame cuts,(cuts 0 0 0).2.1⟩

/-- Native arguments at every source site; values are exact windows of the
carry and the unchanged frame, without any output/child-success premise. -/
theorem args (s : RoundsPre) (k : Fin 10) (z : Fin 32) (limb : Fin 4) (log : RoundsLog)
 (cut : roundsArgs {s with count:=0} k z limb log) :
 log.prefixToken=s.prefixToken ∧ log.round=s.round.val ∧
 log.alphaWord=word (cell s.alpha k) limb ∧ log.runningWord=word s.running limb ∧
 log.stateByte=cell s.state z ∧ log.next=s.next ∧ log.count=1 ∧ log.frame=s.frame := cut.2

/-- The bound needed by the native one-site counter and row cast follows
from the source's fixed ten-call order. -/
theorem domain (r : Usize) (member : r∈NJG_RoundsCode.sites) :
 r.val<10 ∧ r.val<255 ∧ 15+r.val<27 := by
 have bound:=NJG_RoundsCode.sites_domain r member
 omega

#print axioms step
#print axioms args
#print axioms domain
end AspisR1.NJM_RoundsNative
