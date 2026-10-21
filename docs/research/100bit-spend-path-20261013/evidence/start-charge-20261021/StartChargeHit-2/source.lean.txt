import AcceptedAdaptiveFiatShamir
import R1GenericNoHit

set_option autoImplicit false
noncomputable section
namespace AspisR1.StartChargeHit

open FS FS2 R0C.V3
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open AspisR1.AllAddressFiatShamir
open AspisR1.AcceptedAdaptiveFiatShamir
open AspisR1.GenericNoHit

variable {X M C W Pf I A Y : Type}
variable [DecidableEq I] [Inhabited A] [Fintype A]

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
      · refine ⟨⟨0, by simp⟩, ?_⟩
        simpa using hhead
      · obtain ⟨i, hbad⟩ := ih (prev ++ [(m,c)]) htail
        refine ⟨i.succ, ?_⟩
        simpa [List.take_succ_cons, List.append_assoc, List.getElem_cons_succ, Fin.val_succ] using hbad

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

private theorem protocol_transcript_statement
    (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    ∀ n, (pr.transcript H x π n).statement = x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [FS2.Protocol.transcript, Prefix.ext, ih]

private theorem protocol_transcript_prefix_rounds
    (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    ∀ i n, i ≤ n → (pr.transcript H x π i).rounds =
      ((pr.transcript H x π n).rounds).take i := by
  intro i n hi
  rw [protocol_transcript_rounds, protocol_transcript_rounds]
  rw [← List.map_take]
  rw [List.take_range]
  simp [Nat.min_eq_left hi]

/-- A pointwise completion on a specified chronological log suffices.
No acceptance, mass hypothesis, or terminal log is used here. -/
theorem hit_implies_chain
    (pr : FS2.Protocol X M C W Pf I A)
    (bad : Prefix X M C → M → C → Prop)
    (dec : R0C.V3.Dec X M C I A Y)
    (H : I → A) (v : View I A ((X × Pf) × Bool))
    (hreads : ∀ n a, n < pr.r → firstCell (pr.chain H v.2.1.1 v.2.1.2 n) = some a →
      a ∈ v.1.map Prod.fst)
    (hne : ChainsRead pr)
    (hdecodes : ∀ n a, n < pr.r → firstCell (pr.chain H v.2.1.1 v.2.1.2 n) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable v.1 a) = some (own,pend,g) ∧
        bfollow g (traceFrom v.1 a) own pend (tableBefore emptyTable v.1 a) =
          some (pr.transcript H v.2.1.1 v.2.1.2 n, pr.msg v.2.1.2 n,
            pr.chal H v.2.1.1 v.2.1.2 n))
    (hhit : hitFrom bad v.2.1.1 [] (pr.transcript H v.2.1.1 v.2.1.2 pr.r).rounds) :
    hitsChain3 dec (fun p m _t c => bad p m c) emptyTable v.1 := by
  classical
  let x := v.2.1.1
  let π := v.2.1.2
  obtain ⟨i, hbad⟩ := hitFrom_exists_bad bad x []
    (pr.transcript H x π pr.r).rounds hhit
  have hi : i.val < pr.r := by
    simpa only [protocol_transcript_rounds, List.length_map, List.length_range] using i.isLt
  let tr := pr.transcript H x π pr.r
  let Pᵢ := pr.transcript H x π i.val
  have hrows : tr.rounds =
      (List.range pr.r).map (fun j => (pr.msg π j, pr.chal H x π j)) :=
    protocol_transcript_rounds pr H x π pr.r
  have hindex : tr.rounds[i.val]'(by simpa [tr, protocol_transcript_rounds] using hi) =
      (pr.msg π i.val, pr.chal H x π i.val) := by
    have hidx : ((List.range pr.r).map (fun j => (pr.msg π j, pr.chal H x π j)))[i.val]'(by simpa using hi) =
        (pr.msg π i.val, pr.chal H x π i.val) := by simp [hi]
    simpa only [hrows, List.getElem_map] using hidx
  have hprefix : Pᵢ.rounds = tr.rounds.take i.val :=
    protocol_transcript_prefix_rounds pr H x π i.val pr.r (Nat.le_of_lt hi)
  have hp_bad : bad Pᵢ (pr.msg π i.val) (pr.chal H x π i.val) := by
    have hb := hbad
    simp only [List.nil_append] at hb
    rw [hindex] at hb
    have hP : Pᵢ = ⟨x, tr.rounds.take i.val⟩ := by
      change pr.transcript H x π i.val = _
      cases hq : pr.transcript H x π i.val with
      | mk s rs =>
        simp only [Prefix.mk.injEq]
        constructor
        · simpa [hq, Pᵢ, x] using (protocol_transcript_statement pr H x π i.val)
        · simpa [hq, Pᵢ, tr] using
            (protocol_transcript_prefix_rounds pr H x π i.val pr.r (Nat.le_of_lt hi))
    rw [hP]
    exact hb
  have hne := hne i.val (pr.transcript H x π i.val) (pr.msg π i.val) hi
  obtain ⟨a, ha⟩ : ∃ a, firstCell (pr.chain H x π i.val) = some a := by
    cases h : firstCell (pr.chain H x π i.val) with
    | none => exact absurd h hne
    | some a => exact ⟨a, rfl⟩
  have hmem : a ∈ v.1.map Prod.fst := hreads i.val a hi ha
  obtain ⟨own, pend, g, hdecode, hfollow⟩ := hdecodes i.val a hi ha
  apply hitsChain3_of_first dec (fun P m _T c => bad P m c) a v.1 emptyTable hmem rfl
  refine ⟨own, pend, g, Pᵢ, pr.msg π i.val, pr.chal H x π i.val, hdecode, ?_, ?_⟩
  · simpa only [x, π] using hfollow
  · exact hp_bad

#print axioms hitFrom_exists_bad
#print axioms protocol_transcript_rounds
#print axioms protocol_transcript_statement
#print axioms protocol_transcript_prefix_rounds
#print axioms hit_implies_chain
end AspisR1.StartChargeHit
end
