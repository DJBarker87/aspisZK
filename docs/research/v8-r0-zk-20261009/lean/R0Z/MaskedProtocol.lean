import R0P.SemDeg

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

/-- C:392-393, [0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25]. -/
def factorExponent (c : Fin 16) : Fin 27 :=
  ⟨if c.val < 14 then 2 * c.val else if c.val = 14 then 13 else 25,
    by split_ifs <;> omega⟩

/-- C:394-395, [1,3,5,7,9,11,15,17,19,21]. -/
def maskOnlyFactorExponent (c : Fin 10) : Fin 27 :=
  ⟨if c.val < 6 then 2 * c.val + 1 else 2 * c.val + 3,
    by split_ifs <;> omega⟩

/-- C:446-465,535-552: multiplication by (1,i,u,iu), column modulo four. -/
def towerBasis (B : PackBasis F) (j : Fin 4) : K :=
  if j.val = 0 then 1 else if j.val = 1 then B.i else if j.val = 2 then B.u else B.i * B.u

def mulTowerBasis (B : PackBasis F) (v : K) (j : Fin 4) : K := towerBasis B j * v

/-- C:484-492. Family 0 gives 3*S0+22*S1; family 16 gives
275*S0+150*S1, the selected evaluator's two forms (C:494-512). -/
def maskLinear (family : Nat) (α : Fin 10 → K) : K :=
  ∑ j : Fin 10, ((3 + 22 * j.val + family * (17 + 8 * j.val) : Nat) : K) * α j

structure MaskFactors (K : Type) where
  c1 : Fin 16 → K
  maskOnly : Fin 10 → K
  explicitG : K

/-- C:561-580. Exponentiation is the mathematical power table, not a
kernel evaluation of the Rust repeated-multiply/addition-chain algorithms. -/
def maskFactors (B : PackBasis F) (α : Fin 10 → K) : MaskFactors K where
  c1 c := mulTowerBasis B (maskLinear 0 α ^ (factorExponent c).val)
    ⟨c.val % 4, Nat.mod_lt _ (by omega)⟩
  maskOnly c := mulTowerBasis B (maskLinear 0 α ^ (maskOnlyFactorExponent c).val)
    ⟨c.val % 4, Nat.mod_lt _ (by omega)⟩
  explicitG := 1 + maskLinear 16 α ^ 26

/-- C:612-643,647-674: the selected mask, including all ten mask-only
columns. The latter source implementation evaluates the same coefficients
by Horner's rule. D (lane 28) has zero factor and is absent here. -/
def maskValue (B : PackBasis F) (c1 : Fin 16 → K) (maskOnly : Fin 10 → K)
    (g : K) (α : Fin 10 → K) : K :=
  (∑ c, (maskFactors B α).c1 c * c1 c) +
    (maskFactors B α).explicitG * g +
    ∑ c, (maskFactors B α).maskOnly c * maskOnly c

/-- Degree 27 after substituting the committed trace MLEs, rather than
only checking the degree-26 factors with the column values held constant.
All row sums remain behind the existing symbolic MLE degree theorem. -/
theorem maskValue_mldeg (B : PackBasis F) (t : Trace K) :
    MLDeg 27 10 (fun α => maskValue B
      (fun c => honestClaims t α 0 (Fin.castLE (by omega) c))
      (fun c => honestClaims t α 0 ⟨16 + c.val, by omega⟩)
      (honestClaims t α 0 27) α) := by
  classical
  have hlinear (family : Nat) : VDeg 10 (fun _ => 1) (maskLinear (K := K) family) := by
    apply vdeg_sum Finset.univ
    intro j _
    apply vdeg_smul
    apply vdeg_mono (vdeg_proj j)
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> omega
  have hfactor (e : Fin 27) (j : Fin 4) : VDeg 10 (fun _ => 26)
      (fun α => mulTowerBasis B (maskLinear 0 α ^ e.val) j) := by
    apply vdeg_mono (vdeg_smul _ (vdeg_pow (hlinear 0) e.val))
    intro i
    have := e.isLt
    omega
  have hg : VDeg 10 (fun _ => 26) (fun α : Fin 10 → K => 1 + maskLinear 16 α ^ 26) := by
    simpa only [Nat.mul_one, Nat.zero_max] using
      vdeg_add (vdeg_const 10 (fun _ => 0) (1 : K)) (vdeg_pow (hlinear 16) 26)
  apply vdeg_mlDeg (d := fun _ => 27) _ (fun _ => le_refl _)
  unfold maskValue
  apply vdeg_add (d := fun _ => 27) (e := fun _ => 27)
  · apply vdeg_add (d := fun _ => 27) (e := fun _ => 27)
    · apply vdeg_sum Finset.univ
      intro c _
      exact vdeg_mul (hfactor (factorExponent c) _) (vdeg_honestClaims_zero t _)
    · exact vdeg_mul hg (vdeg_honestClaims_zero t 27)
  · apply vdeg_sum Finset.univ
    intro c _
    exact vdeg_mul (hfactor (maskOnlyFactorExponent c) _) (vdeg_honestClaims_zero t _)

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
