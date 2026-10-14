import R1ReseedSamplerLaw
import FS.LemmaB

/-! Follow a one-round reseed sampler under explicit freshness and ordering
hypotheses, with an arbitrary list of pending missing answers. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedOwnFollow

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem follow (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (T : Table (Addr L) State)
    (c : Addr L) (reseed : State → Addr L) (miss : List (Addr L))
    {C : Type} (g : State → List State → C)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hnd : (miss ++ [c, squeezeA p (H c), advanceA p (H c),
      reseed (H (advanceA p (H c)))]).Nodup)
    (hfresh : ∀ b ∈ miss ++ [c, squeezeA p (H c), advanceA p (H c),
      reseed (H (advanceA p (H c)))], T b = none ∧ Read tr b)
    (hsq : Before tr c (squeezeA p (H c)))
    (had : Before tr c (advanceA p (H c)))
    (har : Before tr c (reseed (H (advanceA p (H c)))))
    (hadr : Before tr (advanceA p (H c)) (reseed (H (advanceA p (H c))))) :
    bfollow g tr (ReseedSamplerLaw.own p c reseed)
      (miss.map fun b => (b, (none : Option State))) T =
      some (g (H (reseed (H (advanceA p (H c)))))
        (miss.map H ++ [H (squeezeA p (H c))])) := by
  let sq := squeezeA p (H c)
  let ad := advanceA p (H c)
  let r := reseed (H (advanceA p (H c)))
  let own := ReseedSamplerLaw.own p c reseed
  let pend := miss.map fun b => (b, (none : Option State))
  have hwait : waiting pend = miss := by
    exact DQ.waiting_none miss
  have hevs : evs H own = [(true, c), (false, sq), (true, ad), (true, r)] := by
    simp [own, ReseedSamplerLaw.own, evs, sq, ad, r]
  have hevsAddr : (evs H own).map Prod.snd = [c, sq, ad, r] := by
    rw [hevs]
    rfl
  have hnd' : (waiting pend ++ (evs H own).map Prod.snd).Nodup := by
    rw [hwait, hevsAddr]
    exact hnd
  have hfresh' : ∀ b ∈ waiting pend ++ (evs H own).map Prod.snd,
      T b = none ∧ Read tr b := by
    intro b hb
    rw [hwait, hevsAddr] at hb
    exact hfresh b hb
  have hord : OrderOK tr (evs H own) := by
    rw [hevs]
    simp only [OrderOK]
    constructor
    · intro _ e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he | he
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact hsq
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact had
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact har
    · simpa [ad, r] using hadr
  have hf := bfollow_ok H g tr own pend T hcons hnd' hfresh' hord
  have hfill : fill H pend = miss.map H := by
    simp [pend, fill]
  rw [hfill] at hf
  simpa [own, ReseedSamplerLaw.own, runOut, sq, ad, r] using hf

#print axioms follow

end AspisR1.ReseedOwnFollow
end
