import R0P.MaskProtocol
import R0P.SemDuplexDecoder
import R0C.V3.BSOk
import FS2.DuplexDecodes

/-! G24: generic completing decoder, parameterized by the total round count
and inner semantic message type. The frozen decoder is recovered at 31. -/
set_option autoImplicit false
namespace R0P.MaskDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P R0P.SemSource R0P.SemD3Glue R0P.Mask
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

abbrev CM (SM : Type) := R0C.SemStatement.Msg SemE SemE SM
abbrev CC := Duplex.Chal (R0C.SemStatement.Chal SemE SemE)
abbrev CX (Sfield : Fin 29 → Subfield SemE) := TypedContext SemE Sfield
abbrev CombinedDecode (SM : Type) (Sfield : Fin 29 → Subfield SemE) (L : Nat) :=
  Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
    (Prefix (CX Sfield) (CM SM) CC × CM SM × CC))

variable {SM : Type} {Sfield : Fin 29 → Subfield SemE} {L : Nat}
variable (p : Duplex.Params (CM SM) (R0C.SemStatement.Chal SemE SemE) L)

/-- The transcript/verifier program of the q22 chain: all eight pairs. -/
def combinedChainS {C : Type} (out : List State → List State → C) :
    Nat → State → List State → List State → FS2.Sampler (Addr L) State C
  | 0, _, bs, xs => .done (out bs xs)
  | n + 1, s, bs, xs => .ask (squeezeA p s) fun b => .ask (advanceA p s) fun x =>
      combinedChainS out n x (bs ++ [b]) (xs ++ [x])


/-- The opening projection preserves squeeze and advance addresses. -/
theorem combinedChainS_eq {C : Type} (firstOpening : Nat) (s₀ : State) (out : List State → List State → C) :
    ∀ n s bs xs, combinedChainS p out n s bs xs =
      R0C.V3.DQ.chainS (openingParamsAt firstOpening p s₀) out n s bs xs := by
  intro n
  induction n with
  | zero => intro s bs xs; rfl
  | succ n ih =>
      intro s bs xs
      simp only [combinedChainS, R0C.V3.DQ.chainS]
      congr 1
      funext b
      congr 1
      funext x
      exact ih x (bs ++ [b]) (xs ++ [x])

/-- The completing sampler's own part: absorb, then `n` advance steps with
their squeezes spawned. -/
def combinedChainBS : Nat → State → List State → BS (Addr L) State (List State)
  | 0, _, xs => .done xs
  | n + 1, s, xs => .spawn (squeezeA p s) (.ask (advanceA p s) fun x => combinedChainBS n x (xs ++ [x]))

def combinedNsteps (rounds i : Nat) : Nat := if i < rounds - 1 then 1 else 8

def combinedOutFor (rounds i : Nat) (bs xs : List State) : CC :=
  if i < rounds - 1 then (p.σ i (bs.headD default), xs.getD 1 default)
  else openingChallenge (R0C.V3.DQ.out4 (xs.headD default) bs xs.tail)

/-- Earlier squeeze cells absent from the table. -/
def combinedMissing (T : Table (Addr L) State) (recs : List (Rec (CM SM))) : List (Addr L) :=
  ((recs.map fun r => squeezeA p r.2.1).filter fun c => (T c).isNone).dedup

def combinedAccFrom (cells : List (Addr L)) (as : List State) : Addr L → State :=
  R0P.SemDuplex.combinedAccFrom cells as

def combinedDec (rounds : Nat) (x : CX Sfield) : Dec (CX Sfield) (CM SM) CC (Addr L) State (List State) :=
  fun a T =>
    match parseAbsorb a with
    | none => none
    | some (s, _, data) =>
      match p.dec data, walk p T p.rounds s with
      | some m, some recs =>
          if recs.length < rounds then
            some (.ask a fun s' => combinedChainBS p (combinedNsteps rounds recs.length) s' [s'],
              (combinedMissing p T recs).map fun c => (c, none),
              fun xs as => (completePrefix p x T recs
                  (combinedAccFrom (combinedMissing p T recs) (as.take (combinedMissing p T recs).length)), m,
                combinedOutFor p rounds recs.length (as.drop (combinedMissing p T recs).length) xs))
          else none
      | _, _ => none

/-! ## The law of the completing sampler -/

theorem blaw_combinedChainBS {C : Type} (G : List State → List State → C) (obs : C → ℚ) :
    ∀ (n : Nat) (s : State) (xs : List State) (pre : List (Addr L × Option State)),
      blaw G obs (combinedChainBS p n s xs) pre =
        pmean (fun as => Q22.chainE (fun bs ys => obs (G (xs ++ ys) (as ++ bs))) n) pre := by
  intro n
  induction n with
  | zero =>
      intro s xs pre
      simp only [combinedChainBS, blaw, Q22.chainE, List.append_nil]
  | succ n ih =>
      intro s xs pre
      simp only [combinedChainBS, blaw]
      simp only [ih, R0P.SemDuplex.pmean_snoc]
      rw [← pmean_mean_comm pre (fun x as => mean (fun b => Q22.chainE
        (fun bs ys => obs (G (xs ++ [x] ++ ys) (as ++ [b] ++ bs))) n))]
      apply congrArg (fun F => pmean F pre)
      funext as
      simp only [Q22.chainE]
      rw [mean_comm]
      simp only [List.append_assoc, List.singleton_append]


#print axioms combinedChainS_eq
#print axioms combinedDec
#print axioms blaw_combinedChainBS

/-- Structural equality with the frozen chain, for its original message type. -/
theorem combinedChainBS_31 {L : Nat}
    (p : Duplex.Params R0P.SemDuplex.CM (R0C.SemStatement.Chal SemE SemE) L) :
    ∀ n s xs, combinedChainBS p n s xs = R0P.SemDuplex.combinedChainBS p n s xs := by
  intro n
  induction n with
  | zero => intro s xs; rfl
  | succ n ih =>
      intro s xs
      simp only [combinedChainBS, R0P.SemDuplex.combinedChainBS]
      congr 2
      funext x
      exact ih x (xs ++ [x])

/-- Reinstantiation at 31 preserves the frozen completing decoder exactly. -/
theorem combinedDec_31 {Sfield : Fin 29 → Subfield SemE} {L : Nat}
    (p : Duplex.Params R0P.SemDuplex.CM (R0C.SemStatement.Chal SemE SemE) L)
    (B : PackBasis (Sfield 0)) (x : CX Sfield) :
    combinedDec p 31 x = R0P.SemDuplex.combinedDec p B x := by
  funext a T
  unfold combinedDec R0P.SemDuplex.combinedDec
  cases hparse : parseAbsorb a with
  | none => rfl
  | some triple =>
      obtain ⟨s, lbl, data⟩ := triple
      cases hmsg : p.dec data <;> cases hwalk : walk p T p.rounds s <;>
        simp only [hmsg, hwalk, combinedNsteps, R0P.SemDuplex.combinedNsteps,
          combinedMissing, R0P.SemDuplex.combinedMissing, combinedAccFrom,
          combinedOutFor, R0P.SemDuplex.combinedOutFor, combinedChainBS_31,
          Nat.reduceSub]

/-- The new schedule's decoder is the 32-round instance of the same definition. -/
def combinedDecZ {Sfield : Fin 29 → Subfield SemE} {L : Nat}
    (p : Duplex.Params (MsgZ SemE) (ChalZ SemE) L)
    (x : CX Sfield) := combinedDec p 32 x

#print axioms combinedChainBS_31
#print axioms combinedDec_31
#print axioms combinedDecZ

end
end R0P.MaskDuplex
