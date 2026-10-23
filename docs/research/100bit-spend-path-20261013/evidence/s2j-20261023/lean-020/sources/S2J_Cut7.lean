import S2J_Cut6
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2J
open S2E S2Trust S2H S2E_Reference.S2E_Reference

def nativeReadonlyPublic {W : Type} (_ : S2F.Step) (n : NativeSelections W) : S2F.Outcome PE (NativeSelections W) :=
  match n.1.2 with
  | some p => if readonlyBad p.record then .error .InvalidAccountData n else .next n
  | none => .abort n

def referenceReadonlyPublic {C A E : Type} (_ : S2F.Step) (r : OwnedSelections C A E) : S2F.Outcome PE (OwnedSelections C A E) :=
  match r.1.2 with
  | some p => match readonlyThen p (ok (.Ok ())) with
    | .ok (.Ok ()) => .next r
    | .ok (.Err e) => .error e r
    | .fail _ | .div => .abort r
  | none => .abort r

theorem cut7_stepLaw {W C A E : Type} (L : Library W (World C A E))
    (observe : W → NativeArguments) (fixed : FixedInvocation) (o : Originals W C A E) :
    S2F.StepLaw (CheckpointSelectionRelated L observe fixed) nativeReadonlyPublic referenceReadonlyPublic o .readonlyPublic := by
  intro n r related
  have hp := related.prior.referenceBound
  unfold nativeReadonlyPublic referenceReadonlyPublic
  cases np : n.1.2 <;> cases rp : r.1.2 <;> simp only [np,rp] at hp <;> try contradiction
  · exact .abort related
  · dsimp only
    rw [hp.1,readonly_port]
    split <;> constructor <;> exact related

#print axioms cut7_stepLaw
end AspisR1.S2J
