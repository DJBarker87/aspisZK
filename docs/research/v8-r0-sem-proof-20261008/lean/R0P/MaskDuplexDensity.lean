import R0P.MaskDuplexDecoder
import R0P.SemD2Glue

/-! Round-parameterized protocol and density transfer for the completing decoder. -/
set_option autoImplicit false
namespace R0P.MaskDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P R0P.SemSource R0P.SemD3Glue R0P.Mask
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {SM : Type} {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params (CM SM) (R0C.SemStatement.Chal SemE SemE) L)

/-- A generic schedule with its last round replaced by the eight-pair chain. -/
def combinedProtocolAt (rounds : Nat) (msg : Pf → Nat → CM SM)
    (decode : CombinedDecode SM Sfield L) :
    FS2.Protocol (CX Sfield) (CM SM) CC (Trace SemE) Pf (Addr L) State where
  r := rounds
  msg := msg
  samp := combinedSamplerAt (rounds - 1) p
  decode := decode
  extract := R0C.SemStatement.extract (sourceData B)

/-- The old protocol is an exact instance. -/
theorem combinedProtocolAt_31 {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params R0P.SemDuplex.CM (ChalZ SemE) L)
    (msg : Pf → Nat → R0P.SemDuplex.CM) (decode : R0P.SemDuplex.CombinedDecode Sfield L) :
    combinedProtocolAt B p 31 msg decode = combinedProtocol B p msg decode := by rfl

/-- The masked protocol is the 32-round instance. -/
theorem combinedProtocolAt_32 {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0)) (p : Duplex.Params (MsgZ SemE) (ChalZ SemE) L)
    (msg : Pf → Nat → MsgZ SemE) (decode : CombinedDecode (SemMsgZ SemE) Sfield L) :
    combinedProtocolAt B p 32 msg decode = combinedProtocolZ B p msg decode := by rfl

variable (rounds : Nat)

/-- After fixing the earlier missing squeezes, the completing sampler has
exactly the fresh-answer law of the combined sampler. The absorb answer
remains averaged, including in the eight-pair row. -/
theorem combinedOwn_law (i : Nat) (P : Prefix (CX Sfield) (CM SM) CC) (m : CM SM)
    (a : Addr L) (bad : CC → Prop) :
    blaw (fun xs bs => combinedOutFor p rounds i bs xs) (fun c => indicator (bad c))
      (.ask a fun s' => combinedChainBS p (combinedNsteps rounds i) s' [s']) [] =
    independentMean (combinedSamplerAt (rounds - 1) p i P m).toProgram (fun w => indicator (bad w.2)) := by
  simp only [blaw, blaw_combinedChainBS, pmean, List.nil_append, List.singleton_append]
  by_cases hi : i < rounds - 1
  · simp only [combinedNsteps, if_pos hi, combinedOutFor, Q22.chainE,
      List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
    rw [mean_const]
    simp only [combinedSamplerAt, if_pos hi]
    exact (samp_mean p i P m bad).symm
  · simp only [combinedNsteps, combinedOutFor, List.headD_cons, List.tail_cons,
      combinedSamplerAt, if_neg hi]
    rw [independentMean_ask]
    apply mean_congr
    intro s'
    rw [chainS_independentMean (openingParamsAt (rounds - 1 - 4) p s')
      (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs))
      (fun c => indicator (bad c))]
    simp only [List.nil_append]

#print axioms combinedOwn_law

/-- D2 transfers to the decoder after averaging the missing earlier squeezes. -/
theorem combinedChainDensity_of_D2 (x : CX Sfield) (msg : Pf → Nat → CM SM)
    (decode : CombinedDecode SM Sfield L) (rb : RoundByRound' (CX Sfield) (CM SM) CC (Addr L) State)
    (hD2 : FS2.D2 (combinedProtocolAt B p rounds msg decode) rb) :
    ChainDensity3 (combinedProtocolAt B p rounds msg decode) rb (combinedDec p rounds x) := by
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
          (combinedAccFrom miss (as.take miss.length)), m, combinedOutFor p rounds i (as.drop miss.length) xs))
        (fun out => indicator (d2Bad (combinedProtocolAt B p rounds msg decode) rb
          out.1 out.2.1 T out.2.2))
        (.ask a fun s' => combinedChainBS p (combinedNsteps rounds i) s' [s']) (miss.map fun c => (c, none)) []
      rw [List.append_nil] at hsplit
      rw [hsplit]
      apply pmean_le
      intro as has
      simp only [List.length_map] at has
      set P := completePrefix p x T recs (combinedAccFrom miss as) with hP
      have hG : ∀ (xs bs : List State),
          (completePrefix p x T recs (combinedAccFrom miss ((as ++ bs).take miss.length)), m,
            combinedOutFor p rounds i ((as ++ bs).drop miss.length) xs) = (P, m, combinedOutFor p rounds i bs xs) := by
        intro xs bs
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
          List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
      simp only [hG, blaw, blaw_combinedChainBS, pmean, List.nil_append, List.singleton_append]
      have hround : P.round = i := completePrefix_round p x T recs _
      by_cases hd : P.round < (combinedProtocolAt B p rounds msg decode).r ∧
          ∃ T' : Table (Addr L) State, rb.doomed P T'
      · obtain ⟨hlt, T', hT'⟩ := hd
        have hlaw := combinedOwn_law p rounds i P m a
          (d2Bad (combinedProtocolAt B p rounds msg decode) rb P m T)
        simp only [blaw, blaw_combinedChainBS, pmean, List.nil_append, List.singleton_append] at hlaw
        rw [hlaw]
        have hiff : (fun w : View (Addr L) State CC => indicator (d2Bad
            (combinedProtocolAt B p rounds msg decode) rb P m T w.2)) =
            (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) := by
          funext w
          apply indicator_iff
          exact ⟨fun h => h.2.2, fun h => ⟨hlt, ⟨T', hT'⟩, h⟩⟩
        rw [hiff]
        exact le_trans (hD2 i P m T' T hround (hround ▸ hlt) hT')
          (le_maxErr _ _ i (hround ▸ hlt))
      · have hz : ∀ c : CC, indicator (d2Bad (combinedProtocolAt B p rounds msg decode)
            rb P m T c) = 0 := by
          intro c
          rw [indicator_iff (q := False), indicator_false]
          exact ⟨fun h => hd ⟨h.1, h.2.1⟩, False.elim⟩
        simp only [hz, Q22.chainE_const, mean_const]
        exact maxErr_nonneg _ _
    · cases hdec
  · cases hdec

#print axioms combinedProtocolAt_31
#print axioms combinedProtocolAt_32
#print axioms combinedChainDensity_of_D2
end
end R0P.MaskDuplex
