import LIB_VArray
set_option autoImplicit false
noncomputable section
namespace LIB_VRoundCanonical
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (CanonicalRaw)
open AspisR1 AspisR1PublicPreparation
open PreparedHashCode (run)
open NJG_RoundsCode (Carry sites)
theorem step (p : Prefix) (D : aspis_core.Digest32 Unit) (t : Transcript)
 (a : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31)
 (r : Usize) (bound : r.val<10) (after : Carry Unit)
 (success : (run (S1SemanticCode.roundStep NJM_RoundJoin.R D (prefixRaw p) t a running r)).2=.ok (.Ok after)) :
 CanonicalRaw after.1 := by
 change (run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld p.parsed) t a running r)).2=.ok (.Ok after) at success
 obtain ⟨record,poly,b,_,_,_,cases_⟩ := NJM_RoundRoot.source D p.source p.parsed p.parse_eq t a running r bound
 unfold NJM_RoundRoot.Cases at cases_
 split at cases_
 · have same := congrArg Prod.snd cases_.1
   rw [success] at same
   cases same
 · generalize hchild : run (S1SemanticCode.semanticValidated D t record)=child at cases_
   rcases child with ⟨log,reply⟩
   cases reply with
   | fail e =>
    have same := congrArg Prod.snd cases_
    rw [success] at same
    cases same
   | div =>
    have same := congrArg Prod.snd cases_
    rw [success] at same
    cases same
   | ok pair =>
    rcases pair with ⟨sem,post⟩
    cases sem with
    | Err e =>
     have same := congrArg Prod.snd cases_.1
     rw [success] at same
     cases same
    | Ok q =>
     obtain ⟨value,_,canonical,whole,_⟩ := cases_
     have equal := core.result.Result.Ok.inj (Result.ok.inj
      ((congrArg Prod.snd whole).symm.trans success))
     have scalar := congrArg Prod.fst equal
     exact scalar ▸ canonical
/-- Rule B: one arbitrary source step, induction over the actual returned
carry. No ten independent output witnesses or native loop unfolding. -/
theorem chain (p : Prefix) (D : aspis_core.Digest32 Unit) (rows : List Usize)
 (carry after : Carry Unit) (bounded : ∀ r∈rows,r.val<10) (nonempty : rows≠[])
 (success : (run (NJG_RoundsCode.chain NJM_RoundJoin.R D (prefixRaw p) rows carry)).2=.ok (.Ok after)) :
 CanonicalRaw after.1 := by
 induction rows generalizing carry with
 | nil => exact (nonempty rfl).elim
 | cons r rest ih =>
  have bound := bounded r (by simp)
  rw [NJM_RoundsInvariant.cons_run] at success
  generalize head : run (S1SemanticCode.roundStep NJM_RoundJoin.R D (prefixRaw p) carry.2.2 carry.2.1 carry.1 r)=call at success
  rcases call with ⟨log,reply⟩
  cases reply with
  | fail e => cases success
  | div => cases success
  | ok reply =>
   cases reply with
   | Err e => cases success
   | Ok next =>
    have native : (run (S1SemanticCode.roundStep NJM_RoundJoin.R D (prefixRaw p) carry.2.2 carry.2.1 carry.1 r)).2=.ok (.Ok next) := congrArg Prod.snd head
    by_cases empty : rest=[]
    · subst rest
      have same : next=after := core.result.Result.Ok.inj (Result.ok.inj success)
      subst after
      exact step p D _ _ _ r bound next native
    · exact ih next (fun r mem=>bounded r (by simp [mem])) empty success
/-- Canonical scalar and every alpha slot on the SAME full rounds result. -/
theorem rounds (p : Prefix) (D : aspis_core.Digest32 Unit) (t : Transcript)
 (after : Carry Unit)
 (success : (run (S1SemanticCode.rounds NJM_RoundJoin.R D (prefixRaw p) t)).2=.ok (.Ok after)) :
 CanonicalRaw after.1 ∧ LIB_VArray.Canonical after.2.1 := by
 obtain ⟨running,whole,_⟩ := NJM_RoundsPacket.source D p.source p.parsed p.parse_eq t
 have source := NJM_RoundsJoin.source D p.source p.parsed p.parse_eq sites
  (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t)
 have selected := (congrArg Prod.snd (whole.trans source.symm)).symm.trans success
 refine ⟨chain p D sites _ after NJG_RoundsCode.sites_domain (by decide) selected,?_⟩
 have alpha := NJM_RoundsCanonical.ten D (prefixRaw p) _ after selected
 intro q mem
 obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp mem
 have bound : i<10 := by simpa only [after.2.1.property] using hi
 rw [←same]
 exact alpha ⟨i,bound⟩ bound
#print axioms step
#print axioms chain
#print axioms rounds
end LIB_VRoundCanonical
