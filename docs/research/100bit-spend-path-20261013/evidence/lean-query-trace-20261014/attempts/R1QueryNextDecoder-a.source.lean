import R1QueryNextTrace

/-! A local completing decoder for q22 followed by one duplex round.
It obtains the predecessor state from the queried address, not from an
oracle-dependent argument. Earlier rounds and the full R1 instance remain
separate integration obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryNextDecoder
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev Output (Cv : Type) (L : Nat) := QueryNextLaw.Recovered L × Chal Cv
abbrev Completion (Cv : Type) (L : Nat) :=
  BS (Addr L) State State × List (Addr L × Option State) ×
    (State → List State → Output Cv L)

def decode (p : Params M Cv L) (i : Nat) (c : Addr L) (T : Table (Addr L) State) :
    Option (Completion Cv L) :=
  match parseAbsorb c with
  | none => none
  | some (endpoint, _, _) =>
      match DuplexSeek.seek p T 9 endpoint with
      | none => none
      | some _ => some (QueryNextLaw.own p c,
          (QueryDecoder.missing p T endpoint).map fun b => (b, none),
          QueryNextLaw.output p T endpoint i)

theorem decode_absorb (p : Params M Cv L) (i : Nat) (T : Table (Addr L) State)
    (endpoint : State) (lbl : Byte) (data : Bytes) (hlen : data.length ≤ p.D)
    (hseek : (DuplexSeek.seek p T 9 endpoint).isSome) :
    decode p i (absorbA p endpoint lbl data hlen) T =
      some (QueryNextLaw.own p (absorbA p endpoint lbl data hlen),
        (QueryDecoder.missing p T endpoint).map fun b => (b, none),
        QueryNextLaw.output p T endpoint i) := by
  unfold decode
  rw [parseAbsorb_absorbA]
  cases hs : DuplexSeek.seek p T 9 endpoint with
  | none => rw [hs] at hseek; contradiction
  | some r => rfl

theorem decodes_after_query (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State)
    (hstep : ∀ j < 8, s (j + 1) = H (advanceA p (s j)))
    (hreadadv : ∀ j < 8, Read tr (advanceA p (s j)))
    (hreadsq : ∀ j < 8, Read tr (squeezeA p (s j)))
    (a : Addr L) (haread : Read tr a) (hparsea : (parseAbsorb a).isSome)
    (hroot : s 0 = H a)
    (lbl : Byte) (data : Bytes) (hlen : data.length ≤ p.D)
    (hcread : Read tr (absorbA p (QueryFirstRead.result p H s).2 lbl data hlen))
    (hnewsq : Read tr (squeezeA p (H (absorbA p (QueryFirstRead.result p H s).2 lbl data hlen))))
    (hnewadv : Read tr (advanceA p (H (absorbA p (QueryFirstRead.result p H s).2 lbl data hlen))))
    (i : Nat) :
    let c := absorbA p (QueryFirstRead.result p H s).2 lbl data hlen
    let T := tableBefore emptyTable tr c
    ∃ own pend g, decode p i c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (some (a, QueryFirstRead.result p H s),
          (p.σ i (H (squeezeA p (H c))), H (advanceA p (H c)))) := by
  dsimp only
  let endpoint := (QueryFirstRead.result p H s).2
  let c := absorbA p endpoint lbl data hlen
  let T := tableBefore emptyTable tr c
  have hprefix : c.toBytes.take 32 = bytes endpoint :=
    toBytes_absorbA p endpoint lbl data hlen
  obtain ⟨k, hk, hselected, hseek, _⟩ :=
    QueryFirstRead.recover_query_before_endpoint p H tr Qtot hcons hQ hcoll
      s hstep hreadadv a c haread hcread hparsea hroot hprefix
  have hseekSome : (DuplexSeek.seek p T 9 endpoint).isSome := by
    rw [hseek]
    rfl
  refine ⟨QueryNextLaw.own p c,
    (QueryDecoder.missing p T endpoint).map fun b => (b, none),
    QueryNextLaw.output p T endpoint i,
    decode_absorb p i T endpoint lbl data hlen hseekSome, ?_⟩
  exact QueryNextTrace.follows_after_query p H tr Qtot hcons hQ hcoll
    s hstep hreadadv hreadsq a c haread hcread hparsea
    (by rw [parseAbsorb_absorbA]; rfl) hroot hprefix hnewsq hnewadv i

#print axioms decode_absorb
#print axioms decodes_after_query
end AspisR1.QueryNextDecoder
end
