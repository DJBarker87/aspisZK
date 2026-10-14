import R1ReseedBoundary
import R1ReseedSamplerLaw
import R1TraceSuffixFacts

/-! The row-ending sampler follows the P3 reseed on the actual trace.
Freshness and ordering are derived, including the trailing-state edge. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedTrace
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem follows (p : Params M Cv L) (tag : Byte) (hL : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (a : Addr L) (ha : Read tr a)
    (hsq : Read tr (squeezeA p (H a))) (had : Read tr (advanceA p (H a)))
    (hr : Read tr (OpeningReseedFrame.addr tag hL (H (advanceA p (H a)))))
    (i : Nat) :
    bfollow (fun y bs => (p.σ i (bs.headD default), y)) (traceFrom tr a)
      (ReseedSamplerLaw.own p a (OpeningReseedFrame.addr tag hL)) []
      (tableBefore emptyTable tr a) =
      some (p.σ i (H (squeezeA p (H a))),
        H (OpeningReseedFrame.addr tag hL (H (advanceA p (H a))))) := by
  let sq := squeezeA p (H a)
  let ad := advanceA p (H a)
  let r := OpeningReseedFrame.addr tag hL (H ad)
  let own := ReseedSamplerLaw.own p a (OpeningReseedFrame.addr tag hL)
  let T := tableBefore emptyTable tr a
  let suffix := traceFrom tr a
  have hasq : Before tr a sq :=
    noColl_prefix_after p Qtot H tr hcons hQ hold a sq ha hsq (toBytes_squeezeA p (H a))
  have haad : Before tr a ad :=
    noColl_prefix_after p Qtot H tr hcons hQ hold a ad ha had (toBytes_advanceA p (H a))
  have hadr : Before tr ad r :=
    ParsedStateTrace.parsed_after TrailingStateFrame.tailState Qtot H tr hcons hQ
      htail ad r had hr (OpeningReseedFrame.tailState_addr tag hL (H ad))
  have har := before_trans tr haad hadr
  have hsqad : sq ≠ ad := squeezeA_ne_advanceA p (H a)
  have hsqr : sq ≠ r := by
    intro he
    have hlen := congrArg (fun b : Addr L => b.toBytes.length) he
    have hsqLen : sq.toBytes.length = 33 := by
      simp [sq, squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
    have hrLen : r.toBytes.length = 62 := OpeningReseedFrame.addr_length tag hL (H ad)
    omega
  have hnd : [a, sq, ad, r].Nodup := by
    simp [before_ne tr hasq, before_ne tr haad, before_ne tr har,
      hsqad, hsqr, before_ne tr hadr]
  have hreads : ∀ b ∈ [a, sq, ad, r], Read tr b := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ha
    · exact hsq
    · exact had
    · exact hr
  have hafter : ∀ b ∈ [a, sq, ad, r], b = a ∨ Before tr a b := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hasq
    · exact Or.inr haad
    · exact Or.inr har
  have hfresh : ∀ b ∈ [a, sq, ad, r], T b = none ∧ Read suffix b := by
    intro b hb
    have hn : T b = none := by
      rcases hafter b hb with he | hB
      · rw [he]
        exact tableBefore_self H tr a hcons
      · exact TraceSuffix.after_absent H tr a b hcons hB
    exact ⟨hn, TraceSuffix.absent_read H tr a b hcons ha (hreads b hb) hn⟩
  have hevs : evs H own = [(true, a), (false, sq), (true, ad), (true, r)] := by
    simp [own, ReseedSamplerLaw.own, evs, sq, ad, r]
  have hasq' : Before suffix a sq := DQ.before_traceFrom a a sq tr ha (Or.inl rfl) hasq
  have haad' : Before suffix a ad := DQ.before_traceFrom a a ad tr ha (Or.inl rfl) haad
  have har' : Before suffix a r := DQ.before_traceFrom a a r tr ha (Or.inl rfl) har
  have hadr' : Before suffix ad r := DQ.before_traceFrom a ad r tr ha (Or.inr haad) hadr
  have hord : OrderOK suffix (evs H own) := by
    rw [hevs]
    simp only [OrderOK]
    constructor
    · intro _ e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he | he
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact hasq'
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact haad'
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact har'
    · simp [OrderOK, hadr']
  have hnd' : (waiting ([] : List (Addr L × Option State)) ++ (evs H own).map Prod.snd).Nodup := by
    simpa [waiting, hevs] using hnd
  have hfresh' : ∀ b ∈ waiting ([] : List (Addr L × Option State)) ++ (evs H own).map Prod.snd,
      T b = none ∧ Read suffix b := by
    simpa [waiting, hevs] using hfresh
  have hf := bfollow_ok H (fun y bs => (p.σ i (bs.headD default), y)) suffix own [] T
    (TraceSuffix.traceFrom_consistent H tr a hcons ha) hnd' hfresh' hord
  simpa [own, ReseedSamplerLaw.own, runOut, fill] using hf

#print axioms follows
end AspisR1.ReseedTrace
end
