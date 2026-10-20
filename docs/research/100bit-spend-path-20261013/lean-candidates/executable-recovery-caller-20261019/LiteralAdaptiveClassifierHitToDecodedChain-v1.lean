import AcceptedAdaptiveFiatShamir
import GenericNoHit

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralAdaptiveClassifierHitToDecodedChain

open FS FS2 R0C.V3
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisR1.AllAddressFiatShamir
open AspisR1.AcceptedAdaptiveFiatShamir
open AspisR1.GenericNoHit

variable {X M C W Pf I A Y : Type}
variable [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A]

/-- A hit in a list has a first indexed round witnessing the bad predicate. -/
theorem hitFrom_exists_bad
    (bad : Prefix X M C → M → C → Prop) (x : X) (prev : List (M × C)) :
    ∀ (rs : List (M × C)), hitFrom bad x prev rs →
      ∃ i : Fin rs.length,
        bad ⟨x, prev ++ rs.take i.val⟩ (rs[i.val]'i.isLt).1 (rs[i.val]'i.isLt).2 := by
  intro rs
  induction rs generalizing prev with
  | nil =>
      intro hh
      simp [hitFrom] at hh
  | cons q rest ih =>
      rcases q with ⟨m, c⟩
      intro hh
      simp only [hitFrom] at hh
      rcases hh with hhead | htail
      · refine ⟨0, by simp, ?_⟩
        simpa using hhead
      · obtain ⟨i, hi, hbad⟩ := ih (prev ++ [(m,c)]) htail
        refine ⟨i + 1, by simp [hi], ?_⟩
        simpa only [List.take_succ_cons, List.append_assoc,
          List.getElem_cons_succ] using hbad

/-- An accepted lazy-injection execution with a literal bad transcript round
must contain a decoded first-read chain for that same bad round. The table
argument to `hitsChain3` is ignored by the literal classifier. -/
theorem accepted_hit_implies_decoded_chain
    (pr : FS2.Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop)
    (dec : R0C.V3.Dec X M C I A Y)
    (P : Program I A (X × Pf)) (V : X → Pf → Program I A Bool)
    (κ : Nat → ℚ) (Qtot : Nat)
    (inj : AcceptedAdaptiveFiatShamir.LazyInj pr dec P V κ Qtot)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (H : I → A) (hcoll : ¬ inj.Coll (eval H (AcceptedAdaptiveFiatShamir.experiment P V)))
    (hacc : accepts (eval H (AcceptedAdaptiveFiatShamir.experiment P V)))
    (hhit : hitFrom bad (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1 []
      (pr.transcript H (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.1
        (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).2.1.2 pr.r).rounds) :
    hitsChain3 dec (fun P m _T c => bad P m c) emptyTable
      (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).1 := by
  classical
  let v := eval H (AcceptedAdaptiveFiatShamir.experiment P V)
  let x := v.2.1.1
  let π := v.2.1.2
  obtain ⟨i, hbad⟩ := hitFrom_exists_bad bad x []
    (pr.transcript H x π pr.r).rounds hhit
  have hi : i.val < pr.r := by
    simpa only [FS2.transcript_round] using i.isLt
  let tr := pr.transcript H x π pr.r
  let Pᵢ := pr.transcript H x π i.val
  have hrows : tr.rounds =
      (List.range pr.r).map (fun j => (pr.msg π j, pr.chal H x π j)) :=
    FS2.transcript_rounds
  have hindex : tr.rounds[i.val]'(by simpa [tr, FS2.transcript_round] using i.isLt) =
      (pr.msg π i.val, pr.chal H x π i.val) := by
    rw [hrows]
    simp only [List.getElem_map, List.getElem_range]
  have hprefix : Pᵢ = ⟨x, tr.rounds.take i.val⟩ := by
    cases Pᵢ with
    | mk px prs =>
      apply Prefix.ext
      · rfl
      · rw [FS2.transcript_rounds, FS2.transcript_rounds]
        simp [tr, Pᵢ, List.take_map, List.take_range, hi]
  have hp_bad : bad Pᵢ (pr.msg π i.val) (pr.chal H x π i.val) := by
    have hb := hbad
    rw [hindex] at hb
    simpa [hprefix] using hb
  have hne := hreads i (pr.transcript H x π i.val) (pr.msg π i) hi
  obtain ⟨a, ha⟩ : ∃ a, firstCell (pr.chain H x π i) = some a := by
    cases h : firstCell (pr.chain H x π i) with
    | none => exact absurd h hne
    | some a => exact ⟨a, rfl⟩
  have hmem : a ∈ v.1.map Prod.fst := by
    have hv := hV H x π i.val a hi ha
    rw [show v = eval H (AcceptedAdaptiveFiatShamir.experiment P V) from rfl,
      AcceptedAdaptiveFiatShamir.experiment, FS2.experiment_eval,
      List.map_append, List.mem_append]
    exact Or.inr hv
  have hdec := inj.decodes H hcoll hacc i.val a hi ha
  apply hitsChain3_of_first dec (fun P m _T c => bad P m c) a v.1 emptyTable hmem rfl
  refine ⟨_, _, _, Pᵢ, pr.msg π i, pr.chal H x π i, hdec.1, hdec.2, ?_⟩
  simpa only [hp_bad]

end AspisR1.LiteralAdaptiveClassifierHitToDecodedChain
end
