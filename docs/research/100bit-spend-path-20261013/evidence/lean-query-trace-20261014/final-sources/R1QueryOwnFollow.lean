import R1QueryNextLaw

/-! Mechanical wrapper: following the one-round own sampler under explicit
freshness, read, and address-order hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryOwnFollow

open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisR1.QueryNextLaw

variable {M Cv : Type} {L : Nat}

theorem follow (p : Params M Cv L) (H : Addr L → State) (tr : List (Addr L × State))
    (T : Table (Addr L) State) (c : Addr L) (miss : List (Addr L))
    {C : Type} (g : State → List State → C)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hnd : (miss ++ [c, squeezeA p (H c), advanceA p (H c)]).Nodup)
    (hfresh : ∀ b ∈ miss ++ [c, squeezeA p (H c), advanceA p (H c)],
      T b = none ∧ Read tr b)
    (hsq : Before tr c (squeezeA p (H c)))
    (had : Before tr c (advanceA p (H c))) :
    bfollow g tr (own p c) (miss.map fun b => (b, (none : Option State))) T =
      some (g (H (advanceA p (H c)))
        (miss.map H ++ [H (squeezeA p (H c))])) := by
  have hwait : waiting (miss.map fun b => (b, (none : Option State))) = miss := by
    exact R0C.V3.DQ.waiting_none miss
  have hevsRaw : evs H (own p c) =
      [(true, c), (false, squeezeA p (H c)), (true, advanceA p (H c))] := by
    simp [own, evs]
  have hevs : (evs H (own p c)).map Prod.snd =
      [c, squeezeA p (H c), advanceA p (H c)] := by
    simp [own, evs]
  have hnd' :
      (waiting (miss.map fun b => (b, (none : Option State))) ++
        (evs H (own p c)).map Prod.snd).Nodup := by
    rw [hwait, hevs]
    exact hnd
  have hfresh' : ∀ b ∈ waiting (miss.map fun b => (b, (none : Option State))) ++
      (evs H (own p c)).map Prod.snd, T b = none ∧ Read tr b := by
    intro b hb
    rw [hwait, hevs] at hb
    exact hfresh b hb
  have hord : OrderOK tr (evs H (own p c)) := by
    rw [hevsRaw]
    simp only [OrderOK]
    constructor
    · intro _ e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact hsq
      · have haddr := congrArg Prod.snd he
        rw [haddr]
        exact had
    · simp [OrderOK]
  have hfollow := bfollow_ok H g tr (own p c)
    (miss.map fun b => (b, (none : Option State))) T hcons hnd' hfresh' hord
  have hfill : fill H (miss.map fun b => (b, (none : Option State))) = miss.map H := by
    simp [fill]
  rw [hfill] at hfollow
  simpa [own, runOut] using hfollow

#print axioms follow

end AspisR1.QueryOwnFollow
end
