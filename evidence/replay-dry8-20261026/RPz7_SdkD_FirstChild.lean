import RPz7_SdkD_FirstOrder
import RPz7_RowShape_InstalledSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_FirstChild
open Aeneas Aeneas.Std Result
open SdkD_Control

abbrev Reply := core.result.Result (alloc.vec.Vec U8) AdapterRw.aspis_r1_cost_probe.verifier.Error

def answer (r : core.result.Result (alloc.vec.Vec U8) AspisR1CurrentCaller.verifier.Error) : Reply :=
  AspisS6CurrentCodecInstallation.mapBoth id AspisS6CurrentVerifierCarrier.fromError r

def execute (ops : AspisR1CurrentCaller.Ops) {Hash : Type}
    (D : AdapterRw.aspis_core.digest.Digest32 Hash)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash)
    (obs : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
    Result (Reply × List Site) :=
  let computed := run (SdkD_First.code ops (AspisS6CurrentFirstInstallation.toDigest D)
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash
    (AspisS6CurrentFirstInstallation.toObserver obs)) []
  match computed.1 with
  | .ok r => .ok (answer r,computed.2)
  | .fail e => .fail e
  | .div => .div

theorem erasure (ops : AspisR1CurrentCaller.Ops) {Hash : Type}
    (D : AdapterRw.aspis_core.digest.Digest32 Hash)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash)
    (obs : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
    S2W_Trace.thenResult (execute ops D semantic pub proof split hash obs) (fun x => .ok x.1) =
      AspisS6CurrentFirstInstallation.current ops D semantic pub proof split hash obs := by
  have source := (SdkD_Control.erasure (SdkD_First.code ops (AspisS6CurrentFirstInstallation.toDigest D)
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash
    (AspisS6CurrentFirstInstallation.toObserver obs)) []).trans
      (SdkD_First.source ops _ hash _ pub proof split _)
  dsimp only [execute]
  unfold AspisS6CurrentFirstInstallation.current
  rw [← source]
  cases (run (SdkD_First.code ops (AspisS6CurrentFirstInstallation.toDigest D)
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash
    (AspisS6CurrentFirstInstallation.toObserver obs)) []).1 <;> rfl

theorem accepted (ops : AspisR1CurrentCaller.Ops) {Hash : Type}
    (D : AdapterRw.aspis_core.digest.Digest32 Hash)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : Hash)
    (obs : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (success : AspisS6CurrentFirstInstallation.current ops D semantic pub proof split hash obs = .ok (.Ok saved)) :
    execute ops D semantic pub proof split hash obs = .ok (.Ok saved,[.batch0,.query0,.save]) := by
  have same := (erasure ops D semantic pub proof split hash obs).trans success
  unfold execute at same ⊢
  generalize computed : run (SdkD_First.code ops (AspisS6CurrentFirstInstallation.toDigest D)
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split hash
    (AspisS6CurrentFirstInstallation.toObserver obs)) [] = pair at same ⊢
  obtain ⟨r,log⟩ := pair
  cases r with
  | fail e => cases same
  | div => cases same
  | ok r =>
    cases r with
    | Err e => cases same
    | Ok value =>
      have equal : value = saved := core.result.Result.Ok.inj (Result.ok.inj same)
      subst value
      have marks := SdkD_FirstOrder.accepted ops _ hash _ pub proof split _ saved [] log computed
      simp only [List.nil_append] at marks
      rw [marks]
      rfl

#print axioms erasure
#print axioms accepted
end AspisR1.SdkD_FirstChild
end
