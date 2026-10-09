import R0P.SemDuplexDecoder
import R0P.SemD2Glue

/-! Density of the combined completing decoder, using the full 31-row D2. -/
set_option autoImplicit false
namespace R0P.SemDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P R0P.SemSource R0P.SemD3Glue
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params CM (R0C.SemStatement.Chal SemE SemE) L)

/-- A flip of the lifted doomed predicate is a source round-bad event. -/
theorem combinedFlip_roundBad (budget : Nat → ℚ) (P : Prefix (CX Sfield) CM CC)
    (m : CM) (c : CC) (T' T : Table (Addr L) State)
    (hd : (duplexRows B budget).doomed P T')
    (hn : ¬ (duplexRows B budget).doomed (P.ext m c) T) :
    R0C.SemStatement.roundBad (sourceData B) (valuePrefix P) m c.1 := by
  apply doomed_ext_roundBad (sourceData B) (valuePrefix P) m c.1 T' T hd
  simpa only [duplexRows, valuePrefix_ext] using hn

/-- After fixing the earlier missing squeezes, the completing sampler has
exactly the fresh-answer law of the combined sampler. The absorb answer
remains averaged, including in the eight-pair row. -/
theorem combinedOwn_law (i : Nat) (P : Prefix (CX Sfield) CM CC) (m : CM)
    (a : Addr L) (bad : CC → Prop) :
    blaw (fun xs bs => combinedOutFor p i bs xs) (fun c => indicator (bad c))
      (.ask a fun s' => combinedChainBS p (combinedNsteps i) s' [s']) [] =
    independentMean (combinedSampler p i P m).toProgram (fun w => indicator (bad w.2)) := by
  simp only [blaw, blaw_combinedChainBS, pmean, List.nil_append, List.singleton_append]
  by_cases hi : i < 30
  · simp only [combinedNsteps, if_pos hi, combinedOutFor, Q22.chainE,
      List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
    rw [mean_const]
    simp only [combinedSampler, if_pos hi]
    exact (samp_mean p i P m bad).symm
  · simp only [combinedNsteps, if_neg hi, combinedOutFor, List.headD_cons, List.tail_cons,
      combinedSampler]
    rw [independentMean_ask]
    apply mean_congr
    intro s'
    rw [chainS_independentMean (openingParams p s')
      (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs))
      (fun c => indicator (bad c))]
    simp only [List.nil_append]

#print axioms combinedFlip_roundBad
#print axioms combinedOwn_law

/-- D2 transfers to the decoder after averaging the missing earlier squeezes. -/
theorem combinedChainDensity_of_D2 (x : CX Sfield) (msg : Pf → Nat → CM)
    (decode : CombinedDecode Sfield L) (budget : Nat → ℚ)
    (hD2 : FS2.D2 (combinedProtocol B p msg decode) (duplexRows B budget)) :
    ChainDensity3 (combinedProtocol B p msg decode) (duplexRows B budget) (combinedDec p B x) := by
  intro a T own pend g hdec
  unfold combinedDec at hdec
  split at hdec
  · cases hdec
  rename_i s lbl data hparse
  split at hdec
  · rename_i m recs hm hwalk
    split at hdec
    · rename_i hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl, rfl⟩ := hdec
      set miss := combinedMissing p T recs with hmiss
      set i := recs.length with hi
      have hsplit := blaw_split (fun xs as => (completePrefix p x T recs
          (combinedAccFrom miss (as.take miss.length)), m, combinedOutFor p i (as.drop miss.length) xs))
        (fun out => indicator (d2Bad (combinedProtocol B p msg decode) (duplexRows B budget)
          out.1 out.2.1 T out.2.2))
        (.ask a fun s' => combinedChainBS p (combinedNsteps i) s' [s']) (miss.map fun c => (c, none)) []
      rw [List.append_nil] at hsplit
      rw [hsplit]
      apply pmean_le
      intro as has
      simp only [List.length_map] at has
      set P := completePrefix p x T recs (combinedAccFrom miss as) with hP
      have hG : ∀ (xs bs : List State),
          (completePrefix p x T recs (combinedAccFrom miss ((as ++ bs).take miss.length)), m,
            combinedOutFor p i ((as ++ bs).drop miss.length) xs) = (P, m, combinedOutFor p i bs xs) := by
        intro xs bs
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
          List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
      simp only [hG, blaw, blaw_combinedChainBS, pmean, List.nil_append, List.singleton_append]
      have hround : P.round = i := completePrefix_round p x T recs _
      by_cases hd : P.round < (combinedProtocol B p msg decode).r ∧
          ∃ T' : Table (Addr L) State, (duplexRows B budget).doomed P T'
      · obtain ⟨hlt, T', hT'⟩ := hd
        have hlaw := combinedOwn_law p i P m a
          (d2Bad (combinedProtocol B p msg decode) (duplexRows B budget) P m T)
        simp only [blaw, blaw_combinedChainBS, pmean, List.nil_append, List.singleton_append] at hlaw
        rw [hlaw]
        have hiff : (fun w : View (Addr L) State CC => indicator (d2Bad
            (combinedProtocol B p msg decode) (duplexRows B budget) P m T w.2)) =
            (fun w => indicator (¬ (duplexRows B budget).doomed (P.ext m w.2) T)) := by
          funext w
          apply indicator_iff
          exact ⟨fun h => h.2.2, fun h => ⟨hlt, ⟨T', hT'⟩, h⟩⟩
        rw [hiff]
        exact le_trans (hD2 i P m T' T hround (hround ▸ hlt) hT')
          (le_maxErr _ _ i (hround ▸ hlt))
      · have hz : ∀ c : CC, indicator (d2Bad (combinedProtocol B p msg decode)
            (duplexRows B budget) P m T c) = 0 := by
          intro c
          rw [indicator_iff (q := False), indicator_false]
          exact ⟨fun h => hd ⟨h.1, h.2.1⟩, False.elim⟩
        simp only [hz, Q22.chainE_const, mean_const]
        exact maxErr_nonneg _ _
    · cases hdec
  · cases hdec

/-- Full chain density with the same four source decoder identities as D2. -/
theorem combinedChainDensity (x : CX Sfield) (msg : Pf → Nat → CM)
    (decode : CombinedDecode Sfield L) (_hr31 : p.rounds = 31)
    (hσsem : ∀ (i : Nat) (_hi : i < 24) (s : State),
      p.σ i s = R0C.SemStatement.Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 24 s = R0C.SemStatement.Chal.circle (circleSample s))
    (hσz1 : ∀ s : State, p.σ 25 s = R0C.SemStatement.Chal.circle (circleSample s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (26 + j.val) s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ j.val s)) :
    ChainDensity3 (combinedProtocol B p msg decode) (duplexRows B combinedD2Budget)
      (combinedDec p B x) :=
  combinedChainDensity_of_D2 B p x msg decode combinedD2Budget
    (combinedProtocol_D2 B p msg decode hσsem hσz0 hσz1 hσopen)

#print axioms combinedChainDensity_of_D2
#print axioms combinedChainDensity
end
end R0P.SemDuplex
