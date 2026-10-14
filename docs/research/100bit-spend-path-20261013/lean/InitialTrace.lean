import R1InitialSamplerLaw
import R1PublicInitFrame
import R1TraceSuffixFacts

/-! Actual first-read trace following for initialization plus row zero. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialTrace
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (init : Addr L) (hi : Read tr init)
    (ha : Read tr (PublicInitFrame.row0 p hD (H init)))
    (hsq : Read tr (squeezeA p (H (PublicInitFrame.row0 p hD (H init)))))
    (had : Read tr (advanceA p (H (PublicInitFrame.row0 p hD (H init)))))
    (i : Nat) :
    bfollow (fun x bs => (p.σ i (bs.headD default), x)) (traceFrom tr init)
      (InitialSamplerLaw.own p init (PublicInitFrame.row0 p hD)) []
      (tableBefore emptyTable tr init) =
      some (p.σ i (H (squeezeA p (H (PublicInitFrame.row0 p hD (H init))))),
        H (advanceA p (H (PublicInitFrame.row0 p hD (H init))))) := by
  let a := PublicInitFrame.row0 p hD (H init)
  let sq := squeezeA p (H a)
  let ad := advanceA p (H a)
  let own := InitialSamplerLaw.own p init (PublicInitFrame.row0 p hD)
  let T := tableBefore emptyTable tr init
  let suffix := traceFrom tr init
  have hia : Before tr init a :=
    noColl_prefix_after p Qtot H tr hcons hQ hold init a hi ha
      (PublicInitFrame.row0_prefix p hD (H init))
  have hasq : Before tr a sq :=
    noColl_prefix_after p Qtot H tr hcons hQ hold a sq ha hsq (toBytes_squeezeA p (H a))
  have haad : Before tr a ad :=
    noColl_prefix_after p Qtot H tr hcons hQ hold a ad ha had (toBytes_advanceA p (H a))
  have hisq := before_trans tr hia hasq
  have hiad := before_trans tr hia haad
  have hnd : [init, a, sq, ad].Nodup := by
    simp [before_ne tr hia, before_ne tr hisq, before_ne tr hiad,
      before_ne tr hasq, before_ne tr haad, squeezeA_ne_advanceA p (H a), sq, ad]
  have hreads : ∀ b ∈ [init, a, sq, ad], Read tr b := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hi
    · exact ha
    · exact hsq
    · exact had
  have hafter : ∀ b ∈ [init, a, sq, ad], b = init ∨ Before tr init b := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hia
    · exact Or.inr hisq
    · exact Or.inr hiad
  have hfresh : ∀ b ∈ [init, a, sq, ad], T b = none ∧ Read suffix b := by
    intro b hb
    have hn : T b = none := by
      rcases hafter b hb with he | hB
      · rw [he]
        exact tableBefore_self H tr init hcons
      · exact TraceSuffix.after_absent H tr init b hcons hB
    exact ⟨hn, TraceSuffix.absent_read H tr init b hcons hi (hreads b hb) hn⟩
  have hevs : evs H own = [(true, init), (true, a), (false, sq), (true, ad)] := by
    simp [own, InitialSamplerLaw.own, evs, a, sq, ad]
  have hia' : Before suffix init a := DQ.before_traceFrom init init a tr hi (Or.inl rfl) hia
  have hisq' : Before suffix init sq := DQ.before_traceFrom init init sq tr hi (Or.inl rfl) hisq
  have hiad' : Before suffix init ad := DQ.before_traceFrom init init ad tr hi (Or.inl rfl) hiad
  have hasq' : Before suffix a sq := DQ.before_traceFrom init a sq tr hi (Or.inr hia) hasq
  have haad' : Before suffix a ad := DQ.before_traceFrom init a ad tr hi (Or.inr hia) haad
  have hord : OrderOK suffix (evs H own) := by
    rw [hevs]
    simp [OrderOK, hia', hisq', hiad', hasq', haad']
  have hnd' : (waiting ([] : List (Addr L × Option State)) ++ (evs H own).map Prod.snd).Nodup := by
    simpa [waiting, hevs] using hnd
  have hfresh' : ∀ b ∈ waiting ([] : List (Addr L × Option State)) ++ (evs H own).map Prod.snd,
      T b = none ∧ Read suffix b := by
    simpa [waiting, hevs] using hfresh
  have hf := bfollow_ok H (fun x bs => (p.σ i (bs.headD default), x)) suffix own [] T
    (TraceSuffix.traceFrom_consistent H tr init hcons hi) hnd' hfresh' hord
  simpa [own, InitialSamplerLaw.own, runOut, fill] using hf

#print axioms follows
end AspisR1.InitialTrace
end
