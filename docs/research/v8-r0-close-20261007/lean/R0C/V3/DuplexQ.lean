import R0C.V3.Gen
import R0C.V3.BSOk
import R0C.V3.Q22Law
import R0C.OpeningSamplerBounds
import R0C.SlackStatement
import R0C.ConcreteSlack
import R0C.SlackDensity
import FS2.DuplexDecodes

/-! # R0 on the duplex with the q22 round: protocol, decoder, chain density

Rounds 0–3 are FS2's one-block duplex rounds with the concrete 32-byte field
sampler (`σQ`).  Round 4 absorbs `F`, then reads all eight (squeeze, advance)
pairs of the q22 chain and scans them (`chainS`); a failed scan gives the
empty set, which the decision rejects.  The decoder's completing sampler asks
the absorb and the chain's advance cells in order and spawns every squeeze
cell, so squeezes may be read in any order; earlier squeezes still missing
from the table are the initial background cells. -/
set_option autoImplicit false
namespace R0C.V3.DQ

open FS FS2 FS2.Duplex R0FS R0FS.V2 R0C.V3
open AspisR0.Opening AspisR0.ListsResponses AspisWideTower
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

abbrev E := WideExact

variable {Sfield : Fin 29 → Subfield E} {Pf : Type} {L : Nat}

/-- The concrete field challenge of rounds 0–3. -/
def σQ : Nat → State → R0FS.Chal E
  | 0, s => .field (R0C.ModuloField.gamma s)
  | _ + 1, s => .field (R0C.ModuloField.ordinary s)

abbrev DC := Duplex.Chal (R0FS.Chal E)

def toChal4 (r : AspisV8R19.Q22SamplerProgram.Result) : DC := (.set (Q22.chalSet r.1), r.2)

def out4 (s' : State) (bs xs : List State) : DC := toChal4 (Q22.scanOut 8 Q22.q0 bs xs s')

variable (p : Duplex.Params (Msg E) (R0FS.Chal E) L)

/-- The transcript/verifier program of the q22 chain: all eight pairs. -/
def chainS {C : Type} (out : List State → List State → C) :
    Nat → State → List State → List State → FS2.Sampler (Addr L) State C
  | 0, _, bs, xs => .done (out bs xs)
  | n + 1, s, bs, xs => .ask (squeezeA p s) fun b => .ask (advanceA p s) fun x =>
      chainS out n x (bs ++ [b]) (xs ++ [x])

def sampQ (i : Nat) (P : Prefix (Stmt E Sfield) (Msg E) DC) (m : Msg E) :
    FS2.Sampler (Addr L) State DC :=
  if i < 4 then Duplex.samp p i P m
  else .ask (absorbA p (stateOf p P) (p.lbl i) (p.enc m) (p.encLen m)) fun s' =>
    chainS p (out4 s') 8 s' [] []

def protocolQ (x : Stmt E Sfield) (msg : Pf → Nat → Msg E) :
    FS2.Protocol (Stmt E Sfield) (Msg E) DC (Fin 29 → AspisPool.AlgorithmicCircleDecoderV7.InitialMessage E)
      Pf (Addr L) State where
  r := p.rounds
  msg := msg
  samp := sampQ p
  decode := fun _ _ => none
  extract := fun x T => extr x T

/-! ## The decoder -/

/-- The completing sampler's own part: absorb, then `n` advance steps with
their squeezes spawned. -/
def chainBS : Nat → State → List State → BS (Addr L) State (List State)
  | 0, _, xs => .done xs
  | n + 1, s, xs => .spawn (squeezeA p s) (.ask (advanceA p s) fun x => chainBS n x (xs ++ [x]))

def nsteps (i : Nat) : Nat := if i < 4 then 1 else 8

def outFor (i : Nat) (bs xs : List State) : DC :=
  if i < 4 then (p.σ i (bs.headD default), xs.getD 1 default)
  else out4 (xs.headD default) bs xs.tail

/-- Earlier squeeze cells absent from the table. -/
def missingQ (T : Table (Addr L) State) (recs : List (Rec (Msg E))) : List (Addr L) :=
  ((recs.map fun r => squeezeA p r.2.1).filter fun c => (T c).isNone).dedup

def accFrom (cells : List (Addr L)) (as : List State) : Addr L → State :=
  fun c => ((cells.zip as).lookup c).getD default

def decQ (x : Stmt E Sfield) : Dec (Stmt E Sfield) (Msg E) DC (Addr L) State (List State) :=
  fun a T =>
    match parseAbsorb a with
    | none => none
    | some (s, _, data) =>
      match p.dec data, walk p T p.rounds s with
      | some m, some recs =>
          if recs.length < 5 then
            some (.ask a fun s' => chainBS p (nsteps recs.length) s' [s'],
              (missingQ p T recs).map fun c => (c, none),
              fun xs as => (completePrefix p x T recs
                  (accFrom (missingQ p T recs) (as.take (missingQ p T recs).length)), m,
                outFor p recs.length (as.drop (missingQ p T recs).length) xs))
          else none
      | _, _ => none

/-! ## The law of the completing sampler -/

theorem pmean_snoc (c : Addr L) (f : List State → ℚ) (pre : List (Addr L × Option State)) :
    pmean f (pre ++ [(c, none)]) = pmean (fun as => mean (fun b => f (as ++ [b]))) pre := by
  rw [pmean_append]
  rfl

theorem blaw_chainBS {C : Type} (G : List State → List State → C) (obs : C → ℚ) :
    ∀ (n : Nat) (s : State) (xs : List State) (pre : List (Addr L × Option State)),
      blaw G obs (chainBS p n s xs) pre =
        pmean (fun as => Q22.chainE (fun bs ys => obs (G (xs ++ ys) (as ++ bs))) n) pre := by
  intro n
  induction n with
  | zero =>
      intro s xs pre
      simp only [chainBS, blaw, Q22.chainE, List.append_nil]
  | succ n ih =>
      intro s xs pre
      simp only [chainBS, blaw]
      simp only [ih, pmean_snoc]
      rw [← pmean_mean_comm pre (fun x as => mean (fun b => Q22.chainE
        (fun bs ys => obs (G (xs ++ [x] ++ ys) (as ++ [b] ++ bs))) n))]
      apply congrArg (fun F => pmean F pre)
      funext as
      simp only [Q22.chainE]
      rw [mean_comm]
      simp only [List.append_assoc, List.singleton_append]

/-! ## Flips are round-bad events -/

theorem flip_roundBad (P : Prefix (Stmt E Sfield) (Msg E) DC) (m : Msg E) (c : DC)
    (T' T : Table (Addr L) State) (hd : R0FS.V2.rb2.doomed P T') (hn : ¬ R0FS.V2.rb2.doomed (P.ext m c) T) :
    R0FS.roundBad (proj P).statement (proj P).rounds m c.1 := by
  change R0FS.doomed (proj P) T' at hd
  change ¬ R0FS.doomed (proj (P.ext m c)) T at hn
  rw [proj_ext] at hn
  obtain ⟨hw, hg⟩ := hd
  simp only [R0FS.doomed, Prefix.ext, not_and, not_not] at hn
  rcases (R0FS.good_append _ _ m c.1).mp (hn hw) with h | h
  · exact absurd h hg
  · exact h

/-! ## Per-round bounds -/

theorem scale_le (k : Nat) (a b : ℚ) (hab : a ≤ b) :
    (k : ℚ) * a ≤ (k : ℚ) * b := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)

theorem round_field_bound (x : Stmt E Sfield) (l : List (Msg E × R0FS.Chal E)) (m : Msg E)
    (i : Nat) (hi : i < 4) (hl : l.length = i) :
    mean (fun b : State => indicator (R0FS.roundBad x l m (σQ i b))) ≤
      R0C.SlackStatement.epsilonSlack E R0C.SlackStatement.delta0 i := by
  have hg := R0C.ConcreteSlack.gamma_budget
  have ho := R0C.ConcreteSlack.ordinary_budget
  have hδ := R0C.ConcreteSlack.delta0_nonneg
  have hz : ∀ (j : Nat), (∀ c, ¬ R0FS.roundBad x l m c) →
      mean (fun b : State => indicator (R0FS.roundBad x l m (σQ j b))) ≤
        R0C.SlackStatement.epsilonSlack E R0C.SlackStatement.delta0 i := by
    intro j hn
    rw [mean_congr (fun b => indicator_iff (iff_false_intro (hn _))), indicator_false, mean_const]
    exact R0C.SlackDensity.epsilonSlack_nonneg hδ i
  unfold R0C.SlackStatement.epsilonSlack
  match i, hi with
  | 0, _ =>
      by_cases hs : ∃ y, l = [] ∧ m = .values y
      · obtain ⟨y, rfl, rfl⟩ := hs
        calc mean (fun b : State => indicator (R0FS.roundBad x [] (.values y) (σQ 0 b)))
            = mean (fun b : State => indicator (R0C.ModuloField.gamma b ∈ bad0 x y)) := by
              apply mean_congr; intro b; apply indicator_iff
              rw [R0FS.rb0]; simp [σQ]
          _ ≤ (336869026605739+14000 : ℚ) * (257 / (256^32 : ℚ)) :=
              R0C.OpeningSamplerBounds.gamma_bad_density x y
          _ ≤ (1 + R0C.SlackStatement.delta0) * ε E 0 := by
              change _ ≤ (1 + R0C.SlackStatement.delta0) *
                ((336869026605739 + 14000 : ℚ) / ((Fintype.card E : ℚ) - 1))
              have := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℚ) ≤ 336869026605739 + 14000)
              have e2 : (1 + R0C.SlackStatement.delta0) *
                  ((336869026605739 + 14000 : ℚ) / ((Fintype.card E : ℚ) - 1)) =
                  (336869026605739 + 14000 : ℚ) *
                    ((1 + R0C.SlackStatement.delta0) / ((Fintype.card E : ℚ) - 1)) := by ring
              rw [e2]
              exact this
      · exact hz 0 fun c h => by
          rcases R0FS.roundBad_shape x l m c h with ⟨_, y, hl', hm⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hs ⟨y, hl', hm⟩
          all_goals omega
  | 1, _ =>
      by_cases hs : ∃ y γ v, l = [(.values y, .field γ)] ∧ m = .scalar v
      · obtain ⟨y, γ, v, rfl, rfl⟩ := hs
        calc mean (fun b : State => indicator (R0FS.roundBad x [(.values y, .field γ)] (.scalar v) (σQ 1 b)))
            = mean (fun b : State => indicator (R0C.ModuloField.ordinary b ∈ bad1 x y γ v)) := by
              apply mean_congr; intro b; apply indicator_iff
              rw [R0FS.rb1]; simp [σQ]
          _ ≤ 300 * (257 / (256^32 : ℚ)) := R0C.OpeningSamplerBounds.kappa_bad_density x y γ v
          _ = (1 + R0C.SlackStatement.delta0) * ε E 1 := by
              change _ = (1 + R0C.SlackStatement.delta0) * ((300 : ℚ) / (Fintype.card E : ℚ))
              rw [ho]; ring
          _ ≤ _ := le_rfl
      · exact hz 1 fun c h => by
          rcases R0FS.roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨_, y, γ, v, hl', hm⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · exact hs ⟨y, γ, v, hl', hm⟩
          all_goals omega
  | 2, _ =>
      by_cases hs : ∃ y γ v κ, l = [(.values y, .field γ), (.scalar v, .field κ)] ∧ m = .unit
      · obtain ⟨y, γ, v, κ, rfl, rfl⟩ := hs
        calc mean (fun b : State => indicator
              (R0FS.roundBad x [(.values y, .field γ), (.scalar v, .field κ)] .unit (σQ 2 b)))
            = mean (fun b : State => indicator (R0C.ModuloField.ordinary b ∈ bad2 x y γ v κ)) := by
              apply mean_congr; intro b; apply indicator_iff
              rw [R0FS.rb2]; simp [σQ]
          _ ≤ 200 * (257 / (256^32 : ℚ)) := R0C.OpeningSamplerBounds.tau_bad_density x y γ v κ
          _ = (1 + R0C.SlackStatement.delta0) * ε E 2 := by
              change _ = (1 + R0C.SlackStatement.delta0) * ((200 : ℚ) / (Fintype.card E : ℚ))
              rw [ho]; ring
          _ ≤ _ := le_rfl
      · exact hz 2 fun c h => by
          rcases R0FS.roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, y, γ, v, κ, hl', hm⟩ |
            ⟨h1, _⟩ | ⟨h1, _⟩
          · omega
          · omega
          · exact hs ⟨y, γ, v, κ, hl', hm⟩
          all_goals omega
  | 3, _ =>
      by_cases hs : ∃ y γ v κ τ Q,
          l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] ∧ m = .poly Q
      · obtain ⟨y, γ, v, κ, τ, Q, rfl, rfl⟩ := hs
        calc mean (fun b : State => indicator (R0FS.roundBad x
              [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ)] (.poly Q) (σQ 3 b)))
            = mean (fun b : State => indicator (R0C.ModuloField.ordinary b ∈ bad3 x y γ κ τ Q)) := by
              apply mean_congr; intro b; apply indicator_iff
              rw [R0FS.rb3]; simp [σQ]
          _ ≤ (9396508281246+600 : ℚ) * (257 / (256^32 : ℚ)) :=
              R0C.OpeningSamplerBounds.alpha_bad_density x y γ κ τ Q
          _ = (1 + R0C.SlackStatement.delta0) * ε E 3 := by
              change _ = (1 + R0C.SlackStatement.delta0) * ((9396508281246 + 600 : ℚ) / (Fintype.card E : ℚ))
              rw [ho]; ring
          _ ≤ _ := le_rfl
      · exact hz 3 fun c h => by
          rcases R0FS.roundBad_shape x l m c h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
            ⟨_, y, γ, v, κ, τ, Q, hl', hm⟩ | ⟨h1, _⟩
          · omega
          · omega
          · omega
          · exact hs ⟨y, γ, v, κ, τ, Q, hl', hm⟩
          · omega

theorem round_q22_bound (x : Stmt E Sfield) (l : List (Msg E × R0FS.Chal E)) (m : Msg E)
    (hl : l.length = 4) (s' : State) :
    Q22.chainE (fun bs ys => indicator (R0FS.roundBad x l m (out4 s' bs ys).1)) 8 ≤
      R0C.SlackStatement.epsilonSlack E R0C.SlackStatement.delta0 4 := by
  have hδ := R0C.ConcreteSlack.delta0_nonneg
  have h4 : ε E 4 ≤ R0C.SlackStatement.epsilonSlack E R0C.SlackStatement.delta0 4 := by
    unfold R0C.SlackStatement.epsilonSlack
    have : 0 ≤ ε E 4 := by
      show (0 : ℚ) ≤ (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith
  by_cases hs : ∃ y γ v κ τ Q α F,
      l = [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ), (.poly Q, .field α)] ∧
        m = .final F
  · obtain ⟨y, γ, v, κ, τ, Q, α, F, rfl, rfl⟩ := hs
    by_cases hM : (matchingFibres (data x y) γ α F).card ≤ 9557
    · refine le_trans ?_ h4
      calc Q22.chainE (fun bs ys => indicator (R0FS.roundBad x _ (.final F) (out4 s' bs ys).1)) 8
          ≤ Q22.chainE (fun bs ys => indicator ((Q22.chalSet (Q22.scanOut 8 Q22.q0 bs ys s').1).card = 22 ∧
              Q22.chalSet (Q22.scanOut 8 Q22.q0 bs ys s').1 ⊆ matchingFibres (data x y) γ α F)) 8 := by
            apply Q22.chainE_mono
            intro bs ys
            apply indicator_mono
            intro h
            rw [R0FS.rb4] at h
            obtain ⟨S, hS, _, hc, hsub⟩ := h
            simp only [out4, toChal4] at hS
            cases hS
            exact ⟨hc, hsub⟩
        _ ≤ _ := Q22.q22_bound s' _ hM
    · have hz : ∀ bs ys, indicator (R0FS.roundBad x
          [(.values y, .field γ), (.scalar v, .field κ), (.unit, .field τ), (.poly Q, .field α)]
          (.final F) (out4 s' bs ys).1) = 0 := by
        intro bs ys
        rw [indicator_iff (q := False), indicator_false]
        constructor
        · intro h
          rw [R0FS.rb4] at h
          obtain ⟨S, _, hb, _, _⟩ := h
          exact hM hb
        · exact False.elim
      calc _ = Q22.chainE (fun _ _ => (0 : ℚ)) 8 := by
            congr 1; funext bs ys; exact hz bs ys
        _ = 0 := Q22.chainE_const 0 8
        _ ≤ _ := R0C.SlackDensity.epsilonSlack_nonneg hδ 4
  · have hz : ∀ bs ys, indicator (R0FS.roundBad x l m (out4 s' bs ys).1) = 0 := by
      intro bs ys
      rw [indicator_iff (q := False), indicator_false]
      refine ⟨fun h => ?_, False.elim⟩
      rcases R0FS.roundBad_shape x l m _ h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨_, y, γ, v, κ, τ, Q, α, F, hl', hm⟩
      · omega
      · omega
      · omega
      · omega
      · exact hs ⟨y, γ, v, κ, τ, Q, α, F, hl', hm⟩
    calc _ = Q22.chainE (fun _ _ => (0 : ℚ)) 8 := by
          congr 1; funext bs ys; exact hz bs ys
      _ = 0 := Q22.chainE_const 0 8
      _ ≤ _ := R0C.SlackDensity.epsilonSlack_nonneg hδ 4

#print axioms blaw_chainBS
#print axioms flip_roundBad
#print axioms round_field_bound
#print axioms round_q22_bound
end
end R0C.V3.DQ
