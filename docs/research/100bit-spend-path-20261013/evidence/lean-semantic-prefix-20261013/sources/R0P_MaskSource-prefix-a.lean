import R0P.MaskBadSets
import R0P.MaskDuplexDecoder

/-! The masked source instance and duplex state predicate. The payment
witness and extractor are unchanged; semantic and opening indices shift. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 FS2.Duplex R0C.SemStatement R0P R0P.SemSource R0P.SemD3Glue
open AspisV8R19.MemoizedProgramLaw AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8PairedCommitment AspisR0.ChordGeometry
noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def sourceDataWithFallbackZ (fallback1 : Point K) (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    {Sfield : Fin 29 → Subfield K} {F : Subfield K} (B : PackBasis F) :
    SourceData (K := K) (E := K) (TypedContext K Sfield) (SemMsgZ K) (Trace K) Sfield where
  semanticRounds := 25
  circleFallback1 := fallback1
  semanticBad := semanticBadZ maskClaims B
  paymentWitness := fun x t => InputNoteExtracted x.pub t
  openingView := openingViewZ
  decision := decisionZ maskClaims B

def sourceDataZ (maskClaims : (Fin 29 → SemE) → (Fin 29 → SemE) → (Fin 10 → SemE) → SemE)
    {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE} (B : PackBasis F) :=
  sourceDataWithFallbackZ (Sfield := Sfield) circleFallback1 maskClaims B

def duplexRowsZ (maskClaims : (Fin 29 → SemE) → (Fin 29 → SemE) → (Fin 10 → SemE) → SemE)
    {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE} (B : PackBasis F)
    {S I A : Type} (budget : Nat → ℚ) :
    FS2.RoundByRound' (TypedContext SemE Sfield) (MsgZ SemE) (ChalZ SemE × S) I A where
  doomed := fun P T => doomed (sourceDataZ maskClaims B) (valuePrefix P) T
  ε := budget

def combinedDecisionZ (maskClaims : (Fin 29 → SemE) → (Fin 29 → SemE) → (Fin 10 → SemE) → SemE)
    {Sfield : Fin 29 → Subfield SemE} (B : PackBasis (Sfield 0))
    (P : FS.Prefix (TypedContext SemE Sfield) (MsgZ SemE) (Duplex.Chal (ChalZ SemE)))
    (m : MsgZ SemE) : Bool := decisionZ maskClaims B (valuePrefix P) m

/-- The outer source extension leaves the payment extractor unchanged. -/
theorem extractZ_eq (maskClaims : (Fin 29 → SemE) → (Fin 29 → SemE) → (Fin 10 → SemE) → SemE)
    {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE} (B : PackBasis F)
    {I A : Type} (x : TypedContext SemE Sfield) (T : Table I A) :
    extract (sourceDataZ maskClaims B) x T = extract (sourceData B) x T := by rfl

theorem combinedD1Z (maskClaims : (Fin 29 → SemE) → (Fin 29 → SemE) → (Fin 10 → SemE) → SemE)
    {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat} (B : PackBasis (Sfield 0))
    (p : Duplex.Params (MsgZ SemE) (ChalZ SemE) L) (msg : Pf → Nat → MsgZ SemE)
    (decode : R0P.MaskDuplex.CombinedDecode (SemMsgZ SemE) Sfield L) (budget : Nat → ℚ) :
    FS2.D1 (combinedProtocolZ B p msg decode) (duplexRowsZ maskClaims B budget) := by
  intro x T hx
  change extract (sourceData B) x T = none at hx
  change (¬ ∃ w, InputNoteExtracted x.pub w) ∧ ¬ hitFrom (sourceDataZ maskClaims B) x [] []
  constructor
  · intro hw
    have hw' : ∃ w, (sourceData B).paymentWitness x w := hw
    rw [extract, dif_pos hw'] at hx
    cases hx
  · exact fun h => h

/-- Select a bad row without enumerating the semantic prefix. -/
theorem roundBadZ_hitFrom {X W : Type} {Sfield : Fin 29 → Subfield K}
    (s : SourceData (K := K) (E := K) X (SemMsgZ K) W Sfield) (x : X) :
    ∀ (rs prev : List (MsgZ K × ChalZ K)) (i : Nat) (hi : i < rs.length),
      roundBad s ⟨x, prev ++ rs.take i⟩ (rs[i]'hi).1 (rs[i]'hi).2 → hitFrom s x prev rs := by
  intro rs
  induction rs with
  | nil => intro prev i hi; simp at hi
  | cons q rs ih =>
      intro prev i hi hbad
      rcases q with ⟨m,c⟩
      cases i with
      | zero =>
          left
          simpa only [List.take_zero, List.append_nil, List.getElem_cons_zero] using hbad
      | succ i =>
          right
          apply ih (prev ++ [(m,c)]) i (by simp only [List.length_cons] at hi; omega)
          simpa only [List.take_succ_cons, List.getElem_cons_succ, List.append_assoc,
            List.singleton_append] using hbad

omit [Fintype K] in
theorem opening_head_at_27 {Sfield : Fin 29 → Subfield K}
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K))
    (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (hview : openingViewZ P = some Q) :
    P.rounds[27]? = Q.rounds.head?.map (fun q => (Msg.opening q.1, Chal.opening q.2)) := by
  obtain ⟨sem, cs, hw, gw, y, y₀, z₀, z₁, hcs, hb, hne, h₀, h₁, os,
    hsem, hparse, hc2, hrounds, hQ⟩ := openingViewZ_some_structure P Q hview
  subst Q
  rw [hrounds, List.getElem?_append_right (by omega), hsem]
  rw [show 27 - 25 = 2 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ,
    ← List.head?_eq_getElem?]
  simp only [openingPairsZ, List.head?_map]

theorem combined_chal27 {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0)) (p : Duplex.Params (MsgZ SemE) (ChalZ SemE) L)
    (msg : Pf → Nat → MsgZ SemE)
    (decode : R0P.MaskDuplex.CombinedDecode (SemMsgZ SemE) Sfield L)
    (hσ27 : ∀ s, p.σ 27 s = .opening (R0C.V3.DQ.σQ 0 s))
    (H : Addr L → State) (x : TypedContext SemE Sfield) (π : Pf) :
    ∃ a : State, ((combinedProtocolZ B p msg decode).chal H x π 27).1 =
      .opening (.field (R0C.ModuloField.gamma a)) := by
  let P27 := (combinedProtocolZ B p msg decode).transcript H x π 27
  let a : State := H (squeezeA p (H (absorbA p (stateOf p P27)
    (p.lbl 27) (p.enc (msg π 27)) (p.encLen (msg π 27)))))
  refine ⟨a, ?_⟩
  change (eval H (combinedSamplerAt 31 p 27 P27 (msg π 27)).toProgram).2.1 =
    .opening (.field (R0C.ModuloField.gamma a))
  rw [combinedSamplerAt, if_pos (show 27 < 31 by omega), oneBlock_value]
  change p.σ 27 a = .opening (.field (R0C.ModuloField.gamma a))
  simpa only [R0C.V3.DQ.σQ] using hσ27 a

#print axioms sourceDataZ
#print axioms extractZ_eq
#print axioms combinedD1Z
#print axioms roundBadZ_hitFrom
#print axioms opening_head_at_27
#print axioms combined_chal27
end
end R0P.Mask
