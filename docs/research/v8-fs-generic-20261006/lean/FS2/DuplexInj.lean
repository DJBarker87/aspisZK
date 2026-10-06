import FS2.DuplexDensity

/-! # The duplex (INJ) and the end-to-end duplex theorem

`DecodesSpec` is the deterministic content of (INJ) for the duplex: outside
the collision event, every transcript round's absorb cell decodes, at the
table of its first read, to a completing sampler that is followed to the
round's prefix, message and challenge.  With `coll_mass` it assembles the
`Inj` structure; with `chainDensity` and the generic theorem it gives the
duplex Fiat–Shamir bound `Q_tot · max_i ε_i + 2·Q_tot²/2^256`.

`DecodesSpec` is stated here and left as the remaining obligation; its
proof is the table-walk argument (ordering of chain reads and uniqueness of
outputs outside the collision event). -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

variable {M Cv X W Pf : Type} {L : Nat}

/-- Every round's sampler reads the oracle (it starts with the absorb read). -/
theorem chainsRead (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W) :
    ChainsRead (protocol p x msg extract) := by
  intro i P m _
  simp [protocol, samp, firstCell]

/-- The deterministic content of (INJ) for the duplex. -/
def DecodesSpec (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W)
    (P : Program (Addr L) State Pf) (V : X → Pf → Program (Addr L) State Bool) (Qtot : Nat) :
    Prop :=
  let pr := protocol p x msg extract
  ∀ H : Addr L → State, ¬ Coll p Qtot (eval H (experiment P V x)) →
    ∀ i a, i < pr.r →
      let v := eval H (experiment P V x)
      firstCell (pr.chain H x v.2.1 i) = some a →
      ∃ S, pr.decode a (tableBefore emptyTable v.1 a) = some S ∧
        follow S (tableBefore emptyTable v.1 a) (traceFrom v.1 a) =
          some (pr.transcript H x v.2.1 i, pr.msg v.2.1 i, pr.chal H x v.2.1 i)

/-- (INJ) for the duplex from the collision mass and `DecodesSpec`. -/
def inj (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W)
    (P : Program (Addr L) State Pf) (V : X → Pf → Program (Addr L) State Bool) (Qtot : Nat)
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot)
    (hdec : DecodesSpec p x msg extract P V Qtot) :
    Inj (protocol p x msg extract) P V x κ Qtot where
  Coll := Coll p Qtot
  mass := coll_mass p Qtot P V x hQ
  decodes := hdec

/-- The duplex Fiat–Shamir bound. -/
theorem duplex_fiat_shamir (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W)
    (rb : RoundByRound' X M (Chal Cv) (Addr L) State)
    (P : Program (Addr L) State Pf) (V : X → Pf → Program (Addr L) State Bool) (Qtot : Nat)
    (hD1 : FS2.D1 (protocol p x msg extract) rb)
    (hD2 : FS2.D2 (protocol p x msg extract) rb)
    (hD3 : FS2.D3 (protocol p x msg extract) rb V)
    (hV : ReadsChains (protocol p x msg extract) V)
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot)
    (hdec : DecodesSpec p x msg extract P V Qtot) :
    mean (fun H : Addr L → State =>
        indicator (accepts (eval H (experiment P V x)) ∧
          extractFails (protocol p x msg extract) x (eval H (experiment P V x)))) ≤
      (Qtot : ℚ) * maxErr rb.ε p.rounds + κ Qtot :=
  theorem4 (protocol p x msg extract) rb P V x κ Qtot hD1
    (chainDensity p x msg extract rb hD2) hD3 (chainsRead p x msg extract) hV
    (inj p x msg extract P V Qtot hQ hdec) hQ

#print axioms duplex_fiat_shamir
#print axioms chainDensity
#print axioms coll_mass
end
end FS2.Duplex
