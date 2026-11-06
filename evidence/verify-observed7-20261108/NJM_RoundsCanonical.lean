import NJM_RoundsInduction
set_option autoImplicit false
namespace AspisR1.NJM_RoundsCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (run)

/-- Internal rule-B invariant proof over the exact source sequence. The
success premise belongs only to this local branch lemma, never the positive
native root. All intermediate carries are recovered from the original body. -/
theorem chain {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (rows : List Usize) (start : Nat) (carry after : Carry H)
 (order : rows.map UScalar.val=List.range' start rows.length) (bound : start+rows.length≤10)
 (canonical : NJM_RoundsInvariant.Inv start carry)
 (success : (run (NJG_RoundsCode.chain NJM_RoundJoin.R D pre rows carry)).2=ok (.Ok after)) :
 NJM_RoundsInvariant.Inv (start+rows.length) after := by
 induction rows generalizing start carry with
 | nil=>
   have same : carry=after := core.result.Result.Ok.inj (Result.ok.inj success)
   subst after
   simpa only [List.length_nil,Nat.add_zero] using canonical
 | cons r rest ih=>
   have ordered : r.val=start ∧ rest.map UScalar.val=List.range' (start+1) rest.length := by
    simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using order
   have rb : r.val<10 := by simp only [List.length_cons] at bound;omega
   rw [NJM_RoundsInvariant.cons_run] at success
   generalize call : run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)=head at success
   rcases head with ⟨log,reply⟩
   cases reply with
   | fail e=>cases success
   | div=>cases success
   | ok reply=>
     cases reply with
     | Err e=>cases success
     | Ok next=>
       have stepCall : (run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)).2=ok (.Ok next) := congrArg Prod.snd call
       have before : NJM_RoundsInvariant.Inv r.val carry := by simpa only [ordered.1] using canonical
       have afterStep:=NJM_RoundsInvariant.step D pre carry next r rb before stepCall
       have afterInv : NJM_RoundsInvariant.Inv (start+1) next := by simpa only [ordered.1] using afterStep
       change (run (NJG_RoundsCode.chain NJM_RoundJoin.R D pre rest next)).2=ok (.Ok after) at success
       have tail:=ih (start+1) next ordered.2 (by simp only [List.length_cons] at bound;omega) afterInv success
       simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

/-- All ten actual challenge slots are canonical on the complete driver's
return; this discharges the later terminal's all-alpha caller domain. -/
theorem ten {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (carry after : Carry H)
 (success : (run (NJG_RoundsCode.chain NJM_RoundJoin.R D pre sites carry)).2=ok (.Ok after)) :
 NJG_CanonicalPrefix.CanonicalBefore after.2.1 10 := by
 have order : sites.map UScalar.val=List.range' 0 sites.length := by decide
 exact chain D pre sites 0 carry after order (by decide) (NJG_CanonicalPrefix.initial _) success

#print axioms chain
#print axioms ten
end AspisR1.NJM_RoundsCanonical
