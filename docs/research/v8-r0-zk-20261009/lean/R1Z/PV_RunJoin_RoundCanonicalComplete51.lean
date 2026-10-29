import R1Z.PV_RunJoin_RoundCanonicalPhase51
import R1Z.PV_RunJoin_SemanticArray50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCanonicalComplete51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
open PV_RunJoin_RoundCanonicalStep51 (Good Q)

theorem rounds (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H F : Type} (D : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F) (oracle : F)
    (n : Nat) (round : Usize) (t : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (bound : round.val+n=10) (before : Prefix round.val point) :
    Post (Good 10) (@host_sumcheck.prove_sumcheck_rounds (types base) (selected base heap box ops)
      H F D oi t out point running round oracle) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_RoundThread38.thread D oi oracle n round bound t out point running]
  exact PV_RunJoin_RoundCanonicalPhase51.complete base heap box ops D oi oracle n round t out point running bound before

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H F : Type} (D : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F) (oracle : F)
    (t : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8) (initial : Q) :
    Post (Good 10) (@host_sumcheck.prove_sumcheck (types base) (selected base heap box ops)
      H F D oi t out initial oracle) := by
  unfold host_sumcheck.prove_sumcheck
  apply PV_RunJoin_ResultPost41.bind
  intro zero
  exact rounds base heap box ops D oi oracle 10 0#usize t out (Array.repeat 10#usize zero) initial rfl
    (PV_RunJoin_PointPrefix51.zero _)

theorem produced (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H F : Type} (D : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F) (oracle : F)
    (t next : host_wire.SemanticTranscript H) (out bytes : alloc.vec.Vec U8) (initial final : Q)
    (alpha : Array Q 10#usize)
    (success : @host_sumcheck.prove_sumcheck (types base) (selected base heap box ops)
      H F D oi t out initial oracle=ok (.Ok (alpha,final),next,bytes)) :
    ∀ i,i<10 → ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticArray50.raw 10#usize alpha i) := by
  have post := complete base heap box ops D oi oracle t out initial
  rw [success] at post
  change Prefix 10 alpha at post
  intro i hi
  rw [PV_RunJoin_SemanticArray50.raw,dif_pos hi]
  exact post ⟨i,hi⟩ hi
#print axioms rounds
#print axioms complete
#print axioms produced
end R1Z.PV_RunJoin_RoundCanonicalComplete51
