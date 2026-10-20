import AcceptedAdaptiveFiatShamir
import R1GenericNoHit

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
      · obtain ⟨i, hbad⟩ := ih (prev ++ [(m,c)]) htail
        refine ⟨i.succ, ?_⟩
        simpa only [List.take_succ_cons, List.append_assoc,
          List.getElem_cons_succ] using hbad

private theorem protocol_transcript_rounds
    (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    ∀ n, (pr.transcript H x π n).rounds =
      (List.range n).map (fun j => (pr.msg π j, pr.chal H x π j)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change (pr.transcript H x π n).rounds ++ [(pr.msg π n, pr.chal H x π n)] = _
      rw [ih, List.range_succ, List.map_append, List.map_singleton]

private theorem protocol_transcript_prefix
    (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    ∀ i n, i ≤ n → pr.transcript H x π i =
      ⟨x, (pr.transcript H x π n).rounds.take i⟩ := by
  intro i n
  induction n generalizing i with
  | zero =>
      intro hi
      have : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      intro hi
      cases i with
      | zero => simp [FS2.Protocol.transcript]
      | succ i =>
          have hi' : i ≤ n := by omega
          have hlen : (pr.transcript H x π n).rounds.length = n := by
            rw [protocol_transcript_rounds]
            simp
          rw [FS2.Protocol.transcript, FS.Prefix.ext]
          simp only [List.take_append, hlen]
          rw [ih i n hi']
          simp [hi']

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
    have hlen := protocol_transcript_rounds pr H x π pr.r
    simp only [hlen, List.length_map, List.length_range] at i.isLt
    exact i.isLt
  let tr := pr.transcript H x π pr.r
  let Pᵢ := pr.transcript H x π i.val
  have hrows : tr.rounds =
      (List.range pr.r).map (fun j => (pr.msg π j, pr.chal H x π j)) :=
    protocol_transcript_rounds pr H x π pr.r
  have hindex : tr.rounds[i.val]'(by simpa [tr, protocol_transcript_rounds] using hi) =
      (pr.msg π i.val, pr.chal H x π i.val) := by
    change ((List.range pr.r).map (fun j => (pr.msg π j, pr.chal H x π j)))[i.val]'_ = _
    simp [hi]
  have hprefix : Pᵢ = ⟨x, tr.rounds.take i.val⟩ := by
    apply Prefix.ext
    · rfl
    · rw [protocol_transcript_rounds pr H x π i.val,
          protocol_transcript_rounds pr H x π pr.r]
      simp [tr, Pᵢ, List.take_map, List.take_range, hi]
  have hp_bad : bad Pᵢ (pr.msg π i.val) (pr.chal H x π i.val) := by
    have hb := hbad
    change bad ⟨x, tr.rounds.take i.val⟩ (tr.rounds[i.val]'_) .1 (tr.rounds[i.val]'_).2 at hb
    rw [hindex] at hb
    simpa only [hprefix] using hb
  have hne := hreads i.val (pr.transcript H x π i.val) (pr.msg π i.val) hi
  obtain ⟨a, ha⟩ : ∃ a, firstCell (pr.chain H x π i.val) = some a := by
    cases h : firstCell (pr.chain H x π i.val) with
    | none => exact absurd h hne
    | some a => exact ⟨a, rfl⟩
  have hmem : a ∈ v.1.map Prod.fst := by
    have hv := hV H x π i.val a hi ha
    dsimp [v, AcceptedAdaptiveFiatShamir.experiment]
    rw [FS2.experiment_eval, List.map_append, List.mem_append]
    exact Or.inr hv
  obtain ⟨own, pend, g, hdecode, hfollow⟩ := inj.decodes H hcoll hacc i.val a hi ha
  apply hitsChain3_of_first dec (fun P m _T c => bad P m c) a v.1 emptyTable hmem rfl
  refine ⟨own, pend, g, Pᵢ, pr.msg π i.val, pr.chal H x i.val, hdecode, ?_, ?_⟩
  · simpa only [v, x, π] using hfollow
  · exact hp_bad

end AspisR1.LiteralAdaptiveClassifierHitToDecodedChain
end
