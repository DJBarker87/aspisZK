import NJG_AlphaCarry
set_option autoImplicit false
namespace AspisR1.NJG_CanonicalPrefix
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize

def CanonicalBefore (alpha : Alpha) (n : Nat) : Prop :=
 ∀ j : Fin 10, j.val<n → JFv_RoundArithmetic.Canonical (FJb_TailCell.cell alpha j)

theorem initial (alpha : Alpha) : CanonicalBefore alpha 0 := by
 intro j h; omega

/-- Array frame law: writing the active slot preserves every earlier canonical
slot. No field reduction or native output equation is assumed. -/
theorem set_prefix (alpha : Alpha) (round : Usize) (bound : round.val<10)
 (q : Q) (before : CanonicalBefore alpha round.val)
 (canonical : JFv_RoundArithmetic.Canonical q) :
 CanonicalBefore (alpha.set round q) (round.val+1) := by
 intro j hj
 by_cases equal : j.val=round.val
 · have h : j=⟨round.val,bound⟩ := Fin.ext equal
   subst j
   rw [NJG_AlphaCarry.set_selected alpha round bound q]
   exact canonical
 · have earlier : j.val<round.val := by omega
   have frame : FJb_TailCell.cell (alpha.set round q) j=FJb_TailCell.cell alpha j := by
    simp [FJb_TailCell.cell,Array.set,equal,Ne.symm equal]
   rw [frame]
   exact before j earlier

/-- Carry propagation for one actual semantic step. The step-success premise
belongs to this local invariant lemma, never to an admitted native root. -/
theorem step {H : Type} (R : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
 (alpha next : Alpha) (running value : Q) (round : Usize) (bound : round.val<10)
 (canonical : CanonicalBefore alpha round.val)
 (success : RoundModel.step R D pre before alpha running round=ok (.Ok (value,next,after))) :
 CanonicalBefore next (round.val+1) := by
 obtain ⟨record,q,getter,sampled,updated⟩:=RoundCalls.step_success R D pre before after alpha next running value round
  (NJG_RoundProducer.row round bound) (NJG_RoundProducer.row_add round bound) success
 have qc:=SemanticCallSelectedCanonical.semantic_success_selected_canonical D before after record q sampled
 rw [updated]
 exact set_prefix alpha round bound q canonical ((NJG_AlphaCarry.canonical_iff q).mpr qc)

#print axioms initial
#print axioms set_prefix
#print axioms step
end AspisR1.NJG_CanonicalPrefix
