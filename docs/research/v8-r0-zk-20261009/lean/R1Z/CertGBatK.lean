import R1Z.CertRelK
import Mathlib.Tactic.Ring

/-! D59.2 / D64.2 (hGBat): the `K` model of the G batched columns, in a light module
(Mathlib and `CertRelK` only).

z9.rs:604-640 `unit_functionals`: `phi[co]` is the batched payload of the unit natural
coefficient `e_co` over the read support (round 0: 7 cells, round 1: 7 cells, the opened
folded cells `fpos`, final: 64 cells; the probe's inactive cell `out[0]` is dropped,
z9c.rs `BAT0`).  With `co = 4·d₀ + s₀ = 16·d₁ + 4·s₁ + s₀`:

* round 0 (`r1::round(e_co, w)`, prover.rs:21-25, `PERM = [0,3,2,1]`):
  `c[s₀ + PERM[t]] += w[4d₀ + t]`, times `QUARTER`;
* `q1 = fold(e_co, α₀)` is `α₀^{s₀}` at `d₀`; round 1 is `r1::round(q1, w1)`;
* folded cell `n` (`fpos[n]`): `q1[d₀]·unit_eval(d₀, ·)`, the natural basis value `natP` at the
  stored first-line point `X n`;
* final `e`: `fold(q1, α₁)[e] = α₁^{s₁}α₀^{s₀}` at `e = d₁`.

`ucellP` is that cell; `gbatP` the G column of `Lanes::raw/bal` (z9.rs:1001-1027, li = 10):
`γ^27 · tower(k) · (phi[T r] − [r inactive]·phi[T 0])` (`Ctx::batched`, `beta[r] = phi[π r]`).
The weights are the CertRelK models `wtP`, `w1P`. Nothing is evaluated. -/

set_option autoImplicit false

namespace R1Z.CertRel

open scoped BigOperators

variable {K : Type} [Field K]

/-- Cell `c` of the unit functional at natural coefficient `co`. -/
def ucellP (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (κ α0 α1 Q : K) (X : ℕ → K) (nf co c : ℕ) : K :=
  if c < 7 then
    Q * ∑ t ∈ Finset.range 4,
      (if co % 4 + (4 - t) % 4 = c then wtP A Z T TI Fl κ (4 * (co / 4) + t) else 0)
  else if c < 14 then
    α0 ^ (co % 4) * (Q * ∑ t ∈ Finset.range 4,
      (if co / 4 % 4 + (4 - t) % 4 = c - 7 then w1P A Z T TI Fl κ α0 Q (4 * (co / 16) + t) else 0))
  else if c < 14 + nf then α0 ^ (co % 4) * natP (X (c - 14)) (co / 4) 8
  else if c - (14 + nf) = co / 16 then α1 ^ (co / 4 % 4) * α0 ^ (co % 4) else 0

/-- Cell `c` of the G column at row `r`, limb `k` (`γ` the batching challenge). -/
def gbatP (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K) (γ κ α0 α1 Q i u : K) (X : ℕ → K)
    (nf r k c : ℕ) : K :=
  γ ^ 27 * tbP i u k * (ucellP A Z T TI Fl κ α0 α1 Q X nf (T r) c -
    Fl r * ucellP A Z T TI Fl κ α0 α1 Q X nf (T 0) c)

end R1Z.CertRel
