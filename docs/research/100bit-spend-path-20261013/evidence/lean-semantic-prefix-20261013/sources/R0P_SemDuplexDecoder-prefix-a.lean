import R0P.SemD3Glue
import R0C.V3.BSOk
import FS2.DuplexDecodes

/-! The 31-round completing decoder: thirty single-squeeze rounds followed
by the eight-pair opening chain. R0C is reused without modification. -/
set_option autoImplicit false
namespace R0P.SemDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P R0P.SemSource R0P.SemD3Glue
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

abbrev CM := R0C.SemStatement.Msg SemE SemE (SemMsg SemE)
abbrev CC := Duplex.Chal (R0C.SemStatement.Chal SemE SemE)
abbrev CX (Sfield : Fin 29 → Subfield SemE) := TypedContext SemE Sfield
abbrev CombinedDecode (Sfield : Fin 29 → Subfield SemE) (L : Nat) :=
  Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
    (Prefix (CX Sfield) CM CC × CM × CC))

variable {Sfield : Fin 29 → Subfield SemE} {L : Nat}
variable (p : Duplex.Params CM (R0C.SemStatement.Chal SemE SemE) L)

/-- The transcript/verifier program of the q22 chain: all eight pairs. -/
def combinedChainS {C : Type} (out : List State → List State → C) :
    Nat → State → List State → List State → FS2.Sampler (Addr L) State C
  | 0, _, bs, xs => .done (out bs xs)
  | n + 1, s, bs, xs => .ask (squeezeA p s) fun b => .ask (advanceA p s) fun x =>
      combinedChainS out n x (bs ++ [b]) (xs ++ [x])


/-- The opening projection preserves squeeze and advance addresses. -/
theorem combinedChainS_eq {C : Type} (s₀ : State) (out : List State → List State → C) :
    ∀ n s bs xs, combinedChainS p out n s bs xs =
      R0C.V3.DQ.chainS (openingParams p s₀) out n s bs xs := by
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

def combinedNsteps (i : Nat) : Nat := if i < 30 then 1 else 8

def combinedOutFor (i : Nat) (bs xs : List State) : CC :=
  if i < 30 then (p.σ i (bs.headD default), xs.getD 1 default)
  else openingChallenge (R0C.V3.DQ.out4 (xs.headD default) bs xs.tail)

/-- Earlier squeeze cells absent from the table. -/
def combinedMissing (T : Table (Addr L) State) (recs : List (Rec (CM))) : List (Addr L) :=
  ((recs.map fun r => squeezeA p r.2.1).filter fun c => (T c).isNone).dedup

def combinedAccFrom (cells : List (Addr L)) (as : List State) : Addr L → State :=
  fun c => ((cells.zip as).lookup c).getD default

def combinedDec (_B : PackBasis (Sfield 0)) (x : CX Sfield) : Dec (CX Sfield) (CM) CC (Addr L) State (List State) :=
  fun a T =>
    match parseAbsorb a with
    | none => none
    | some (s, _, data) =>
      match p.dec data, walk p T p.rounds s with
      | some m, some recs =>
          if recs.length < 31 then
            some (.ask a fun s' => combinedChainBS p (combinedNsteps recs.length) s' [s'],
              (combinedMissing p T recs).map fun c => (c, none),
              fun xs as => (completePrefix p x T recs
                  (combinedAccFrom (combinedMissing p T recs) (as.take (combinedMissing p T recs).length)), m,
                combinedOutFor p recs.length (as.drop (combinedMissing p T recs).length) xs))
          else none
      | _, _ => none

/-! ## The law of the completing sampler -/

theorem pmean_snoc (c : Addr L) (f : List State → ℚ) (pre : List (Addr L × Option State)) :
    pmean f (pre ++ [(c, none)]) = pmean (fun as => mean (fun b => f (as ++ [b]))) pre := by
  rw [pmean_append]
  rfl

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
      simp only [ih, pmean_snoc]
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
end
end R0P.SemDuplex
