import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Basic

/-! D64 hRel: the `K` models of builder 4 (`fill_rel`), in a light module (Mathlib only)
shared by the Aeneas specifications (CertRelWeights, CertRelCoef, CertRelFill, which
never import the relR1 layer) and the pure identification (CertRelWId, CertRelData,
which never import Aeneas).  The two sides together exceed the 7,000 MB limit, so the
bridge between them is `RelEntry`, a statement about `ℕ → ZMod p` data only.

The models mirror the extracted functions: `scP, pcP, eqP, hwP, natP, evP, headP` are
the lift-builder helpers (CertLiftBasic `scK … headK`, same bodies), `ellP` the seven
functionals at a row, `wtP` the κ-batched weight, `w1P, w2P` the two dual folds,
`pfP, lfvP` the pair and line folds, `coefM` the relation coefficient, `tbP, wbP` the
QM31 tower basis and the WideExact limb basis. -/

set_option autoImplicit false

namespace R1Z.CertRel

open scoped BigOperators

variable {K : Type} [Field K]

/-- The QM31 tower basis element `k` (`1, i, u, iu`). -/
def tbP (i u : K) (k : ℕ) : K :=
  if k = 0 then 1 else if k = 1 then i else if k = 2 then u else if k = 3 then i * u else 0

/-- The WideExact limb basis element `m` (tower basis, then tower basis times `w`). -/
def wbP (i u w : K) (m : ℕ) : K := if m < 4 then tbP i u m else tbP i u (m - 4) * w

def scP (A : ℕ → K) (n : ℕ) : K := ∏ k ∈ Finset.range n, A (9 - k)

def pcP (A : ℕ → K) (g c : ℕ) : K :=
  if g = 0 then A c
  else if g = 1 then A c + scP A (9 - c) - (A c * scP A (9 - c) + A c * scP A (9 - c))
  else if c = 7 ∨ c = 6 then 1 - A c else A c

def eqP (A : ℕ → K) (g r : ℕ) : K :=
  ∏ i ∈ Finset.range 10, ((1 - pcP A g i) + (((r / 2 ^ (9 - i)) % 2 : ℕ) : K) * (pcP A g i + pcP A g i - 1))

def hwP (A : ℕ → K) (co : ℕ) : K := if co < 28 then A 8 ^ co else if co < 56 then A 9 ^ (co - 28) else 0

def natP (x : K) (m : ℕ) : ℕ → K
  | 0 => 1
  | k + 1 => (1 + ((m % 2 : ℕ) : K) * (x - 1)) * natP (x * x + x * x - 1) (m / 2) k

def evP (x y : K) (co : ℕ) : K := if co % 2 = 0 then natP x (co / 2) 10 else natP x (co / 2) 10 * y

def headP (A Z : ℕ → K) (co r g : ℕ) : K :=
  if g < 3 then eqP A g r else if g = 3 then hwP A co else evP (Z (2 * (g - 4))) (Z (2 * (g - 4) + 1)) co

/-- `ell_k(e_j)` at row `r` (`Fl` the inactive flags, `T` the transport). -/
def ellP (A Z : ℕ → K) (T : ℕ → ℕ) (Fl : ℕ → K) (r k : ℕ) : K :=
  if k = 0 then Fl r else headP A Z (T r) r (k - 1)

/-- The κ-batched weight of message index `j` (row `TI j`). -/
def wtP (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (κ : K) (j : ℕ) : K :=
  ∑ k ∈ Finset.range 7, κ ^ k * ellP A Z T Fl (TI j) k

def w1P (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (κ α0 Q : K) (d : ℕ) : K :=
  Q * ∑ t ∈ Finset.range 4, wtP A Z T TI Fl κ (4 * d + t) * α0 ^ ((4 - t) % 4)

def w2P (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (κ α0 α1 Q : K) (e : ℕ) : K :=
  Q * ∑ t ∈ Finset.range 4, w1P A Z T TI Fl κ α0 Q (4 * e + t) * α1 ^ ((4 - t) % 4)

/-- `pairFoldValue` with the half `H`. -/
def pfP (H c inv l r : K) : K := (l + r) * H + c * ((l - r) * inv)

/-- The line fold of the unit vector at slot `t`. -/
def lfvP (H a i0 i1 i2 : K) (t : ℕ) : K :=
  pfP H (a * a) i2 (pfP H a i0 (if t = 0 then 1 else 0) (if t = 1 then 1 else 0))
    (pfP H a i1 (if t = 2 then 1 else 0) (if t = 3 then 1 else 0))

/-- The Rust `coef(rho, i)` as a `K` value (kind `kd`, query `U`, cell `i`). -/
def coefP (nf : ℕ) (A2 A3 Q : K) (W2 : ℕ → K) (Fp : ℕ → ℕ) (LF NL : ℕ → K) (kd U i : ℕ) : K :=
  if kd = 0 then (if i = 0 then 1 else 0) + (if i = 4 then 1 else 0)
  else if kd = 1 then (if i < 7 then 0 - Q * A2 ^ i else if i = 7 ∨ i = 11 then 1 else 0)
  else if kd = 2 then
    (if i < 7 then 0 else if i < 14 then A3 ^ (i - 7) else if i < 14 + nf then 0 else 0 - W2 (i - (14 + nf)))
  else if kd = 3 then
    (if i < 14 then 0 else if i < 14 + nf then (if Fp (i - 14) = U then 1 else 0) else 0)
  else if i < 14 then 0
  else if i < 14 + nf then (if Fp (i - 14) / 4 = U / 4 then 1 else 0) * LF (Fp (i - 14) % 4)
  else 0 - NL (i - (14 + nf))

/-- The bridge: entry `(x, c)` of the relation matrix `rel` (row-major, width `bw`) is limb
`x mod 8` of an eight-limb value whose WideExact reading (`e` the embedding of the limbs)
is the coefficient `C (x / 8) (c / 8)` times the basis element `c mod 8`. -/
def RelEntry (e : ZMod 2147483647 →+* K) (i u w : K) (rel : ℕ → ZMod 2147483647) (bw q : ℕ)
    (C : ℕ → ℕ → K) : Prop :=
  ∀ x c, x < q → c < bw → ∃ l : ℕ → ZMod 2147483647, rel (x * bw + c) = l (x % 8) ∧
    ∑ k ∈ Finset.range 8, e (l k) * wbP i u w k = C (x / 8) (c / 8) * wbP i u w (c % 8)

end R1Z.CertRel
