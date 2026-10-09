import R0P.SemD3Glue

/-! G24: the masked reference schedule and generic mask polynomial.
The frozen 31-round modules remain unchanged. C2 is the message before
theta at index 2, not an additional challenge round. Eta is at index 14.
See the fixed D3 decision in the privacy LOG at base d2b741325. -/
set_option autoImplicit false
namespace R0P.Mask
open R0P.SemSource R0P.SemDegree R0P.Sumcheck Polynomial
open R0P.SemD3Glue FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
noncomputable section

inductive SemMsgZ (K : Type) [Field K]
  | base (m : SemMsg K)
  | maskSum (claim : K)

abbrev MsgZ (K : Type) [Field K] := R0C.SemStatement.Msg K K (SemMsgZ K)
abbrev ChalZ (K : Type) [Field K] := R0C.SemStatement.Chal K K

inductive RoundKind
  | lam | chi | c2Theta
  | zc (j : Fin 10)
  | mu | eta
  | alpha (j : Fin 10)
  | circle (j : Fin 2)
  | opening (j : Fin 5)

/-- Thirty-two challenge rows, with maskSum sent immediately before eta. -/
def schedule (i : Fin 32) : RoundKind :=
  if h : i.val = 0 then .lam else if h : i.val = 1 then .chi else
  if h : i.val = 2 then .c2Theta else if h : i.val < 13 then .zc ⟨i.val - 3, by omega⟩ else
  if h : i.val = 13 then .mu else if h : i.val = 14 then .eta else
  if h : i.val < 25 then .alpha ⟨i.val - 15, by omega⟩ else
  if h : i.val < 27 then .circle ⟨i.val - 25, by omega⟩ else .opening ⟨i.val - 27, by omega⟩

section Polynomial
variable {K : Type} [Field K]

/-- The coefficient-indexed Libra row is shared with the opening statement. -/
abbrev libraWeight (alpha : Fin 10 → K) := SemSource.libraWeight alpha

def honestExtra (π : Fin 1024 ≃ Fin 1024) (t : Trace K) (alpha : Fin 10 → K)
    (l : Fin 29) : K :=
  AspisR0.RoundNormalization.dot (libraWeight alpha) (coeffsOf π t l)

/-- Atomic degree hypothesis, using the existing coordinate-wise degree API.
There is no SemBadSets.VDeg in the frozen tree: its coordinate-wise version
is SemDegree.VDeg, with dimension and degree vector explicit. -/
def MaskDegree (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K) : Prop :=
  ∀ (π : Fin 1024 ≃ Fin 1024) (t : Trace K), VDeg 10 (fun _ => 27)
    (fun alpha => maskClaims (fun l => honestClaims t alpha 0 l) (honestExtra π t alpha) alpha)

/-- The source terminal with an arbitrary mask function evaluated on the opened claims. -/
def terminalZ (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (pub : Public K) (lam chi theta mu eta : K) (zc : Fin 10 → K)
    {F : Subfield K} (B : PackBasis F) (y : Fin 3 → Fin 29 → K) (yx : Fin 29 → K) (alpha : Fin 10 → K) : K :=
  maskClaims (y 0) yx alpha + eta * terminalValue pub lam chi theta mu zc B y alpha

def virtualPolyZ (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) (eta : K) : (Fin 10 → K) → K :=
  fun alpha => maskClaims (fun l => honestClaims t alpha 0 l) (honestExtra π t alpha) alpha + eta * virtualPoly pub B t pre alpha

/-- Boolean hypercube summation is the same bsumB used by SemRounds
790-795 and SemBadSets' adaptive sumcheck lemmas; no row enumeration. -/
def maskTotal (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K) (π : Fin 1024 ≃ Fin 1024) (t : Trace K) : K :=
  bsumB 10 (fun b => maskClaims (fun l => honestClaims t (ofBool b) 0 l) (honestExtra π t (ofBool b)) (ofBool b))

def originalTotal (pub : Public K) {F : Subfield K} (B : PackBasis F)
    (t : Trace K) (pre : Fin 14 → K) : K :=
  bsumB 10 (fun b => virtualPoly pub B t pre (ofBool b))

theorem virtualPolyZ_total (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) (eta : K) :
    bsumB 10 (fun b => virtualPolyZ maskClaims π pub B t pre eta (ofBool b)) =
      maskTotal maskClaims π t + eta * originalTotal pub B t pre := by
  unfold virtualPolyZ maskTotal originalTotal
  rw [bsumB_add, bsumB_smul]

/-- Addition takes the maximum of the two degree bounds; eta is fixed
before all alpha rows. The original terminal already has degree 27. -/
theorem virtualPolyZ_vdeg (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K) (hMask : MaskDegree maskClaims)
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) (eta : K) :
    VDeg 10 (fun _ => 27) (virtualPolyZ maskClaims π pub B t pre eta) := by
  exact vdeg_add (hMask π t) (vdeg_smul eta (vdeg_virtualPoly pub B t pre))

theorem virtualPolyZ_indDeg (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K) (hMask : MaskDegree maskClaims)
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) {F : Subfield K} (B : PackBasis F) (t : Trace K)
    (pre : Fin 14 → K) (eta : K) :
    IndDeg 27 10 (virtualPolyZ maskClaims π pub B t pre eta) :=
  SemBadSets.mlDeg_indDeg
    (vdeg_mlDeg (virtualPolyZ_vdeg maskClaims hMask π pub B t pre eta) (fun _ => le_rfl))

/-- Same four checks as SemDecision.sumcheckChecks (97-109), now with
claim m' and the masked terminal. The original target is zero. -/
def sumcheckChecksZ (maskClaims : (Fin 29 → K) → (Fin 29 → K) → (Fin 10 → K) → K)
    (pub : Public K) {F : Subfield K} (B : PackBasis F)
    (pre : Fin 14 → K) (eta claim : K) (alpha : Fin 10 → K)
    (polys : Fin 10 → K[X]) (y : Fin 3 → Fin 29 → K) (yx : Fin 29 → K) : Prop :=
  (∀ j : Fin 10, (polys j).natDegree ≤ 27) ∧
  (polys 0).eval 0 + (polys 0).eval 1 = claim ∧
  (∀ j : Fin 9, (polys j.succ).eval 0 + (polys j.succ).eval 1 =
    (polys j.castSucc).eval (alpha j.castSucc)) ∧
  (polys 9).eval (alpha 9) =
    terminalZ maskClaims pub (pre 0) (pre 1) (pre 2) (pre 13) eta (preZc pre) B y yx alpha
end Polynomial

/-- Generic opening offset, shared by the old and new schedules. -/
def openingParamsAt {SM : Type} {L : Nat} (firstOpening : Nat)
    (p : Duplex.Params (R0C.SemStatement.Msg SemE SemE SM) (ChalZ SemE) L)
    (s : State) : Duplex.Params (R0FS.Msg SemE) (R0FS.Chal SemE) L where
  D := p.D
  hL := p.hL
  enc := fun m => p.enc (.opening m)
  encLen := fun m => p.encLen (.opening m)
  dec := fun bytes => match p.dec bytes with
    | some (.opening m) => some m
    | _ => none
  decEnc := fun m => by rw [p.decEnc]
  lbl := fun j => p.lbl (firstOpening + j)
  σ := R0C.V3.DQ.σQ
  iv := s
  rounds := 5

/-- Parameterized final q22 row; all earlier rows are single-squeeze rows. -/
def combinedSamplerAt {X SM : Type} {L : Nat} (last : Nat)
    (p : Duplex.Params (R0C.SemStatement.Msg SemE SemE SM) (ChalZ SemE) L)
    (i : Nat) (P : FS.Prefix X (R0C.SemStatement.Msg SemE SemE SM)
      (Duplex.Chal (ChalZ SemE))) (m : R0C.SemStatement.Msg SemE SemE SM) :
    FS2.Sampler (Addr L) State (Duplex.Chal (ChalZ SemE)) :=
  if i < last then Duplex.samp p i P m
  else .ask (absorbA p (stateOf p P) (p.lbl i) (p.enc m) (p.encLen m)) fun s' =>
    R0C.V3.DQ.chainS (openingParamsAt (last - 4) p s')
      (fun bs xs => openingChallenge (R0C.V3.DQ.out4 s' bs xs)) 8 s' [] []

/-- The frozen sampler is an exact instance of the generic offset definition. -/
theorem combinedSamplerAt_31 {X : Type} {L : Nat}
    (p : Duplex.Params (R0C.SemStatement.Msg SemE SemE (SemMsg SemE)) (ChalZ SemE) L) :
    combinedSamplerAt (X := X) 30 p = R0P.SemD3Glue.combinedSampler p := by
  rfl

def combinedProtocolZ {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params (MsgZ SemE) (ChalZ SemE) L)
    (msg : Pf → Nat → MsgZ SemE)
    (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler (Addr L) State
      (FS.Prefix (TypedContext SemE Sfield) (MsgZ SemE) (Duplex.Chal (ChalZ SemE)) ×
        MsgZ SemE × Duplex.Chal (ChalZ SemE)))) :
    FS2.Protocol (TypedContext SemE Sfield) (MsgZ SemE) (Duplex.Chal (ChalZ SemE))
      (Trace SemE) Pf (Addr L) State where
  r := 32
  msg := msg
  samp := combinedSamplerAt 31 p
  decode := decode
  extract := R0C.SemStatement.extract (sourceData B)

#print axioms SemMsgZ
#print axioms schedule
#print axioms MaskDegree
#print axioms terminalZ
#print axioms virtualPolyZ_total
#print axioms virtualPolyZ_vdeg
#print axioms virtualPolyZ_indDeg
#print axioms sumcheckChecksZ
#print axioms openingParamsAt
#print axioms combinedSamplerAt
#print axioms combinedSamplerAt_31
#print axioms combinedProtocolZ
end
end R0P.Mask
