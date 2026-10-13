import R0C.V3.DuplexQ

/-! # Chain density of the q22 duplex decoder -/
set_option autoImplicit false
namespace R0C.V3.DQ

open FS FS2 FS2.Duplex R0FS R0FS.V2 R0C.V3
open AspisR0.Opening AspisR0.ListsResponses AspisWideTower
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

variable {Sfield : Fin 29 → Subfield E} {Pf : Type} {L : Nat}
variable (p : Duplex.Params (Msg E) (R0FS.Chal E) L)

abbrev rbQ : RoundByRound' (Stmt E Sfield) (Msg E) DC (Addr L) State :=
  R0C.SlackStatement.rb2Slack R0C.SlackStatement.delta0

theorem chainE_one (F : List State → List State → ℚ) :
    Q22.chainE F 1 = mean (fun b : State => mean (fun x : State => F [b] [x])) := rfl

theorem chainDensityQ (x : Stmt E Sfield) (msg : Pf → Nat → Msg E) (hr5 : p.rounds = 5)
    (hσ : ∀ i s, i < 4 → p.σ i s = σQ i s) :
    ChainDensity3 (protocolQ p x msg) (rbQ (Sfield := Sfield)) (decQ p x) := by
  intro a T own pend g hdec
  have hδ := R0C.ConcreteSlack.delta0_nonneg
  have hr : (protocolQ (Sfield := Sfield) p x msg).r = 5 := hr5
  unfold decQ at hdec
  split at hdec
  · cases hdec
  rename_i s lbl data hparse
  split at hdec
  · rename_i m recs hm hwalk
    split at hdec
    · rename_i hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl, rfl⟩ := hdec
      set miss := missingQ p T recs with hmiss
      set i := recs.length with hi
      have hsplit := blaw_split (fun xs as => (completePrefix p x T recs
          (accFrom miss (as.take miss.length)), m, outFor p i (as.drop miss.length) xs))
        (fun out => indicator (d2Bad (protocolQ (Sfield := Sfield) p x msg) (rbQ (Sfield := Sfield))
          out.1 out.2.1 T out.2.2))
        (.ask a fun s' => chainBS p (nsteps i) s' [s']) (miss.map fun c => (c, none)) []
      rw [List.append_nil] at hsplit
      rw [hsplit]
      apply pmean_le
      intro as has
      simp only [List.length_map] at has
      -- the prefix is fixed by the missing answers
      set P := completePrefix p x T recs (accFrom miss as) with hP
      have hG : ∀ (xs bs : List State),
          (completePrefix p x T recs (accFrom miss ((as ++ bs).take miss.length)), m,
            outFor p i ((as ++ bs).drop miss.length) xs) = (P, m, outFor p i bs xs) := by
        intro xs bs
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
          List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
      simp only [hG, blaw]
      rw [← mean_const (X := State) (maxErr (rbQ (Sfield := Sfield) (L := L)).ε (protocolQ (Sfield := Sfield) p x msg).r)]
      apply mean_mono
      intro s'
      rw [blaw_chainBS]
      simp only [pmean, List.nil_append, List.singleton_append]
      have hround : P.round = i := completePrefix_round p x T recs _
      by_cases hd : P.round < (protocolQ (Sfield := Sfield) p x msg).r ∧
          ∃ T', (rbQ (Sfield := Sfield) (L := L)).doomed P T'
      · obtain ⟨hlt, T', hT'⟩ := hd
        have hlt5 : i < 5 := by rw [← hround, ← hr]; exact hlt
        have hprojlen : (proj P).rounds.length = i := by rw [← hround]; exact proj_round P
        have hflip : ∀ c : DC, indicator (d2Bad (protocolQ (Sfield := Sfield) p x msg) (rbQ (Sfield := Sfield))
            P m T c) ≤ indicator (R0FS.roundBad (proj P).statement (proj P).rounds m c.1) := by
          intro c
          apply indicator_mono
          rintro ⟨_, _, hn⟩
          exact flip_roundBad P m c T' T hT' hn
        have hle : R0C.SlackStatement.epsilonSlack E R0C.SlackStatement.delta0 i ≤
            maxErr (rbQ (Sfield := Sfield) (L := L)).ε (protocolQ (Sfield := Sfield) p x msg).r :=
          le_maxErr _ _ i (by rw [hr]; exact hlt5)
        by_cases hi4 : i < 4
        · have hn : nsteps i = 1 := by simp [nsteps, hi4]
          rw [hn, chainE_one]
          refine le_trans ?_ hle
          calc mean (fun b : State => mean (fun x' : State => indicator (d2Bad
                (protocolQ (Sfield := Sfield) p x msg) (rbQ (Sfield := Sfield)) P m T (outFor p i [b] (s' :: [x'])))))
              ≤ mean (fun b : State => indicator (R0FS.roundBad (proj P).statement (proj P).rounds m (σQ i b))) := by
                apply mean_mono; intro b
                rw [← mean_const (X := State) (indicator (R0FS.roundBad (proj P).statement (proj P).rounds m (σQ i b)))]
                apply mean_mono; intro x'
                refine le_trans (hflip _) (le_of_eq ?_)
                simp only [outFor, if_pos hi4, List.headD, hσ i b hi4]
            _ ≤ _ := round_field_bound (proj P).statement (proj P).rounds m i hi4 hprojlen
        · have hi4' : i = 4 := by omega
          have hn : nsteps i = 8 := by simp [nsteps, hi4]
          rw [hn]
          refine le_trans ?_ (hi4' ▸ hle)
          calc Q22.chainE (fun bs ys => indicator (d2Bad (protocolQ (Sfield := Sfield) p x msg)
                (rbQ (Sfield := Sfield)) P m T (outFor p i bs (s' :: ys)))) 8
              ≤ Q22.chainE (fun bs ys => indicator (R0FS.roundBad (proj P).statement (proj P).rounds m
                  (out4 s' bs ys).1)) 8 := by
                apply Q22.chainE_mono
                intro bs ys
                refine le_trans (hflip _) (le_of_eq ?_)
                simp only [outFor, if_neg hi4, List.headD, List.tail_cons]
            _ ≤ _ := round_q22_bound (proj P).statement (proj P).rounds m (hi4' ▸ hprojlen) s'
      · have hz : ∀ c : DC, indicator (d2Bad (protocolQ (Sfield := Sfield) p x msg) (rbQ (Sfield := Sfield))
            P m T c) = 0 := by
          intro c
          rw [indicator_iff (q := False), indicator_false]
          exact ⟨fun h => hd ⟨h.1, h.2.1⟩, False.elim⟩
        simp only [hz]
        rw [Q22.chainE_const]
        exact maxErr_nonneg _ _
    · cases hdec
  · cases hdec

#print axioms chainDensityQ
end
end R0C.V3.DQ
