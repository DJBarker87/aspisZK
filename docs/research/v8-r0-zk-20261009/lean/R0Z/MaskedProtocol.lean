import R0P.MaskValue

/-! Z2 masked reference, source pin d2b7413259a75100db9d1c722d88932bfea28fb9.
C = crates/aspis-core/src/state_only_hiding.rs. The tower coefficients use
R0P.PackBasis, as does the soundness terminal; no claim about the optimized
Rust limb implementation is imported. This is a reference extension, not an
instance of the old 31-round combinedProtocol. See ../../LOG.md. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.MaskedProtocol
open R0P R0P.SemSource R0P.SemDegree R0P.SemBadSets Polynomial

inductive SemMsgZ (K : Type) [Field K]
  | base (msg : SemMsg K)
  | maskSum (s : K)

abbrev Msg (K : Type) [Field K] := R0C.SemStatement.Msg K K (SemMsgZ K)
abbrev Chal (K : Type) [Field K] := R0C.SemStatement.Chal K K

/-- Each constructor names one message/challenge row. C2 is the message of
`c2Theta`, not an additional challenge. The final opening response follows
row 31 and does not create a 33rd round. -/
inductive RoundKind
  | lambda | chi | c2Theta | zerocheck (j : Fin 10) | mu | maskSumEta
  | sumcheck (j : Fin 10) | circle (j : Fin 2) | opening (j : Fin 5)
  deriving DecidableEq

/-- D3: 25 semantic rows, two circle rows and five opening rows. -/
def schedule (i : Fin 32) : RoundKind :=
  if i.val = 0 then .lambda
  else if i.val = 1 then .chi
  else if i.val = 2 then .c2Theta
  else if h : i.val < 13 then .zerocheck ⟨i.val - 3, by omega⟩
  else if i.val = 13 then .mu
  else if i.val = 14 then .maskSumEta
  else if h : i.val < 25 then .sumcheck ⟨i.val - 15, by omega⟩
  else if h : i.val < 27 then .circle ⟨i.val - 25, by omega⟩
  else .opening ⟨i.val - 27, by omega⟩

variable {K : Type} [Field K] {F : Subfield K}

/- The shared soundness/privacy mask definitions have one source of truth. -/
export R0P.Mask (factorExponent maskOnlyFactorExponent towerBasis mulTowerBasis
  maskLinear MaskFactors maskFactors maskValue)

/-- Degree 27 after substituting the committed trace MLEs, rather than
only checking the degree-26 factors with the column values held constant.
All row sums remain behind the existing symbolic MLE degree theorem. -/
theorem maskValue_mldeg (B : PackBasis F) (t : Trace K) :
    MLDeg 27 10 (fun α => maskValue B
      (fun c => honestClaims t α 0 (Fin.castLE (by omega) c))
      (fun c => honestClaims t α 0 ⟨16 + c.val, by omega⟩)
      (honestClaims t α 0 27) α) := by
  exact vdeg_mlDeg (R0P.Mask.maskValue_vdeg B t) (fun _ => le_refl _)

/-- D3, terminal source crates/aspis-statement/src/state_only_terminal.rs:
797-812,844-871: mask + eta * original. All 29 claims stay available. -/
def terminalZ (pub : Public K) (lam chi θ μ η : K) (zc : Fin 10 → K)
    (B : PackBasis F) (y : Fin 3 → Fin 29 → K) (α : Fin 10 → K) : K :=
  maskValue B (fun c => y 0 (Fin.castLE (by omega) c))
    (fun c => y 0 ⟨16 + c.val, by omega⟩) (y 0 27) α +
    η * terminalValue pub lam chi θ μ zc B y α

/-- The new claim and eta are separate inputs to the sumcheck checks.
Semantic challenges 0..24 follow `schedule`; no old round indices reused. -/
def sumcheckChecksZ (pub : Public K) (B : PackBasis F) (maskSum : K)
    (cs : List K) (hcs : cs.length = 25) (polys : Fin 10 → K[X])
    (y : Fin 3 → Fin 29 → K) : Prop :=
  let lam := cs[0]'(by omega)
  let chi := cs[1]'(by omega)
  let θ := cs[2]'(by omega)
  let zc : Fin 10 → K := fun j => cs[3 + j.val]'(by omega)
  let μ := cs[13]'(by omega)
  let η := cs[14]'(by omega)
  let α : Fin 10 → K := fun j => cs[15 + j.val]'(by omega)
  (∀ j : Fin 10, (polys j).natDegree ≤ 27) ∧
  (polys 0).eval 0 + (polys 0).eval 1 = maskSum + η * 0 ∧
  (∀ j : Fin 9, (polys j.succ).eval 0 + (polys j.succ).eval 1 =
    (polys j.castSucc).eval (α j.castSucc)) ∧
  (polys 9).eval (α 9) = terminalZ pub lam chi θ μ η zc B y α

#print axioms SemMsgZ
#print axioms Msg
#print axioms Chal
#print axioms schedule
#print axioms factorExponent
#print axioms maskOnlyFactorExponent
#print axioms towerBasis
#print axioms mulTowerBasis
#print axioms maskLinear
#print axioms maskFactors
#print axioms maskValue
#print axioms maskValue_mldeg
#print axioms terminalZ
#print axioms sumcheckChecksZ
end R0Z.MaskedProtocol
