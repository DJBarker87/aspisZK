import CuSavingsRetainedSemanticBinding
import ExtractedVerifyPrefixReachability
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSemanticInputs
open Aeneas Aeneas.Std Result CuSavingsRetainedSemanticBinding
private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ x,m=.ok x ∧ k x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem verify_finish_witness (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (d : P.D H) (pub : P.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (P.Phase→Result Unit)) (out : P.Verified H)
    (h : verify R B d pub bytes hash obs=.ok (.Ok out)) :
    ∃ pre before challenges source,
      AspisR1PublicPreparation.FinishModel.finish R B (digest d) (toPublic pub) pre before challenges
        (obs.map (fun mark=>fun p=>mark (phase p)))=.ok (.Ok source) ∧ verified source=out := by
  unfold verify at h
  obtain ⟨actual,ha,h⟩ := bind_ok _ _ _ h
  cases actual with
  | Err e => cases h
  | Ok source =>
    have hout : verified source=out := core.result.Result.Ok.inj (Result.ok.inj h)
    obtain ⟨pre,initial,after,challenges,_,_,_,hfinish⟩ :=
      AspisR1PublicPreparation.VerifyPrefix.verify_success
        (AspisR1PublicPreparation.FinishModel.finish R B)
        (digest d) (toPublic pub) bytes hash _ source ha
    exact ⟨pre,after,challenges,source,hfinish,hout⟩

theorem selected_to_libra (q : Q.K)
    (h : AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.SelectedCanonical
      (AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.ToSelected q)) :
    CuSavingsLibraConcrete.canonicalK (libraK (fromK q)) := h

theorem verify_alpha_canonical (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (d : P.D H) (pub : P.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (P.Phase→Result Unit)) (out : P.Verified H)
    (h : verify R B d pub bytes hash obs=.ok (.Ok out)) :
    ∀ i : Fin 10, CuSavingsLibraConcrete.canonicalK
      (libraK (out.alpha.val[i.val]'(by rw [out.alpha.property];exact i.isLt))) := by
  obtain ⟨pre,before,challenges,source,hs,he⟩ := verify_finish_witness R B d pub bytes hash obs out h
  subst out
  intro i
  have hc := CuSavingsRetainedSemanticFinish.alpha_selected_canonical_of_finish_success
    R B (digest d) (toPublic pub) pre before challenges _ source hs i
  simpa only [verified,array,List.getElem_map] using selected_to_libra _ hc

#print axioms verify_finish_witness
#print axioms selected_to_libra
#print axioms verify_alpha_canonical
end AspisR1.CuSavingsRetainedSemanticInputs
