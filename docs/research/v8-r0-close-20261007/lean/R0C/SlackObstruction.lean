import R0C.ConcreteSlack
import R0C.Counting

/-! A3/A4 stop certificate: delta0 does not fix a total one-state q22 law.
The count is evaluated as 22 descending factors, never a large Pascal tree. -/
set_option autoImplicit false
namespace R0C.SlackObstruction
open R0C.SlackStatement AspisWideTower AspisCircleGroupOrder
open AspisV8R19.SourceDuplexStep AspisV8R19.UniformStateFirstHit
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
noncomputable section
attribute [local instance] Classical.propDecidable

theorem positive_event_atom {A : Type} [Fintype A] (p : A → Prop)
    (a0 : A) (h : p a0) :
    1 / (Fintype.card A : ℚ) ≤ mean (fun a => indicator (p a)) := by
  rw [Counting.mean_indicator_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  haveI : Nonempty {a // p a} := ⟨⟨a0,h⟩⟩
  exact_mod_cast Fintype.card_pos

/-- Closed-form arithmetic over 22 factors only. -/
theorem query_count : Nat.choose 262144 22 = 143459390671643080338858006328548634467103740668941284234642666778199466504034122047364474303283200 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [Nat.descFactorial, Nat.factorial]

theorem oneblock_gap :
    (1+delta0) * ((1 : ℚ) / (Nat.choose 262144 22 : ℚ)) < 1 / (256^32 : ℚ) := by
  rw [query_count]
  norm_num [delta0, P]

/-- Unlike the earlier divisibility contradiction, this uses ONLY the query
clauses and applies even after all field atom budgets have been relaxed. -/
theorem noSamplerLawsSlackD {Pf : Type} {L : Nat}
    {Sfield : Fin 29 → Subfield WideExact}
    (p : FS2.Duplex.Params (R0FS.Msg WideExact) (R0FS.Chal WideExact) L)
    (msg : Pf → Nat → R0FS.Msg WideExact) :
    ¬ SamplerLawsSlackD (Sfield := Sfield) delta0 p msg := by
  intro hs
  have hcard := hs.queryCard
  have hmass := hs.queries
  simp only [R0FS.V2.params1] at hcard hmass
  let s0 : State := fun _ => 0
  obtain ⟨S, hS, h22⟩ := hcard s0
  have hlo := positive_event_atom
    (fun s : State => ∃ S', p.σ 4 s = .set S' ∧ S'.card = 22 ∧ S' ⊆ S)
    s0 ⟨S,hS,h22,Finset.Subset.refl S⟩
  rw [state_card] at hlo
  have hhi := hmass S
  rw [h22, Nat.choose_self, Nat.cast_one] at hhi
  exact (not_lt_of_ge (hlo.trans hhi)) oneblock_gap

#print axioms positive_event_atom
#print axioms query_count
#print axioms oneblock_gap
#print axioms noSamplerLawsSlackD
end
end R0C.SlackObstruction
