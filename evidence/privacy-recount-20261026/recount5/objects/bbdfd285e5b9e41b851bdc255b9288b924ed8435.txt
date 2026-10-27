import R1Z.PV_OptB_OffBad
import R1Z.ProverCommitFuelJoin22
import R1Z.QueryScanRealLazyBound
import R1Z.FinalR1PBin
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_Charged
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
open R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (h : HonestProver K) (P : Challenges K → Prop)
  (V : Challenges K → h.Instance → Prop)
  (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (R : RomModel W) (N : Nat) (hN : 0 < N)
  (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle)
  {Adv World Coins : Type}
  (ab : AbortBridge K CommitHandle Aux R1Z.Batched.R1Bat Adv) (adv : Adv)

/-- Coordinates into the EXISTING event spaces. Supplying these maps does
not prove that they are the native run's common coupling. That association
is a source obligation, never a trust item or a probability charge. -/
structure Coordinates (World Coins : Type) where
  retry : h.Instance → World → Coins → Fin ab.N → ab.Coins
  real : h.Instance → World → Coins → W.Tab × (Fin N → SecP)
  lazy : h.Instance → World → Coins → Fin N → AttS (F := F) W Pr
  queries : h.Instance → World → Coins → List ProverCommitSeedEvent19.Entry
  seed : World → Coins → OracleAnswer
  fuel : World → Coins → ProverCommitFuelJoin22.Tape

/-- Literal union of already named events (no OS-unavailability event).
`lazyBad` and `exhQ` are the conservative honest-coupling/mask exceptions
inside the existing model/fresh allowance; `realBad` is its parser event.
This declaration assigns NO mass and introduces NO new budget. -/
def union (c : Coordinates h W Pr N ab World Coins)
    (w : h.Instance) (os : World) (coins : Coins) : Prop :=
  poleBad P h V ab adv x w (c.retry w os coins) ∨
  QueryScanRealLazyBound.lazyBad W Pr R N hN h B outputs x w (c.lazy w os coins) ∨
  FinalR1PBin.exhQ W Pr R N hN h B outputs x w (c.lazy w os coins) ∨
  QueryScanRealFreshMass.realFresh W Pr N h B outputs x w (c.real w os coins) ∨
  (∃ i, QueryScanRealLazyBound.realBad W Pr N h B outputs x w i (c.real w os coins)) ∨
  ProverCommitSeedEvent19.seedGuess (c.queries w os coins) (c.seed os coins) ∨
  ∃ j, ProverCommitFuelJoin22.failure j (c.fuel os coins)

/-- Exact D262 condition on these coordinates. Instances are admitted by
`h.Instance`; both witnesses share public input, OS world and coins. The
signal carrier retains family/position/error (and any observed prefix).
The native HOST_HASH must be fixed in the eventual source interpretation. -/
abbrev AuxiliaryIndependent (c : Coordinates h W Pr N ab World Coins)
    {Event : Type} (signal : h.Instance → World → Coins → Option Event) : Prop :=
  PV_OptB_Factorization.IndependentOffBad h.public signal
    (union h P V W Pr R N hN B outputs x ab adv c)

#print union
#print AuxiliaryIndependent
#print axioms union

variable (c : Coordinates h W Pr N ab World Coins)
  (w : h.Instance) (os : World) (coins : Coins)
theorem off_pole (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ poleBad P h V ab adv x w (c.retry w os coins) := by
  intro event
  exact good (Or.inl (event))
#print axioms off_pole
theorem off_lazy (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ QueryScanRealLazyBound.lazyBad W Pr R N hN h B outputs x w (c.lazy w os coins) := by
  intro event
  exact good (Or.inr (Or.inl (event)))
#print axioms off_lazy
theorem off_mask (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ FinalR1PBin.exhQ W Pr R N hN h B outputs x w (c.lazy w os coins) := by
  intro event
  exact good (Or.inr (Or.inr (Or.inl (event))))
#print axioms off_mask
theorem off_fresh (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ QueryScanRealFreshMass.realFresh W Pr N h B outputs x w (c.real w os coins) := by
  intro event
  exact good (Or.inr (Or.inr (Or.inr (Or.inl (event)))))
#print axioms off_fresh
theorem off_parser (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ (∃ i, QueryScanRealLazyBound.realBad W Pr N h B outputs x w i (c.real w os coins)) := by
  intro event
  exact good (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (event))))))
#print axioms off_parser
theorem off_seed (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ ProverCommitSeedEvent19.seedGuess (c.queries w os coins) (c.seed os coins) := by
  intro event
  exact good (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (event)))))))
#print axioms off_seed
theorem off_fuel (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ (∃ j, ProverCommitFuelJoin22.failure j (c.fuel os coins)) := by
  intro event
  exact good (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (event)))))))
#print axioms off_fuel

variable {Core Address : Type} (M q : Nat)
  (charged : Fin M → Core → Prop) (priv : Fin M → Prop)
  (qry : Fin q → Core → Address) (addr : Fin M → Core → Address)
  (core : h.Instance → World → Coins → Core)

/-- Complete named union, including the model's adversary-hit and private
collision events. Parameters are those supplied by ModelsVR1's existing
couplings. No event is assigned a new charge. Native coordinate association
and the coupling laws are still P obligations. -/
def fullUnion (v : h.Instance) (world : World) (random : Coins) : Prop :=
  union h P V W Pr R N hN B outputs x ab adv c v world random ∨
  R0Z.FsAbortBounds.HitEv M q charged qry addr (core v world random) ∨
  R0Z.FsAbortBounds.CollEv M priv addr (core v world random)

abbrev HeadlineIndependent {Event : Type}
    (signal : h.Instance → World → Coins → Option Event) : Prop :=
  PV_OptB_Factorization.IndependentOffBad h.public signal
    (fullUnion h P V W Pr R N hN B outputs x ab adv c M q charged priv qry addr core)

#print fullUnion
#print HeadlineIndependent
#print axioms fullUnion
theorem off_full_auxiliary (v : h.Instance) (world : World) (random : Coins)
    (good : ¬ fullUnion h P V W Pr R N hN B outputs x ab adv c M q charged priv qry addr core v world random) :
    ¬ union h P V W Pr R N hN B outputs x ab adv c v world random :=
  fun event => good (Or.inl event)

#print axioms off_full_auxiliary
theorem off_full_hit (v : h.Instance) (world : World) (random : Coins)
    (good : ¬ fullUnion h P V W Pr R N hN B outputs x ab adv c M q charged priv qry addr core v world random) :
    ¬ R0Z.FsAbortBounds.HitEv M q charged qry addr (core v world random) :=
  fun event => good (Or.inr (Or.inl event))

#print axioms off_full_hit
theorem off_full_collision (v : h.Instance) (world : World) (random : Coins)
    (good : ¬ fullUnion h P V W Pr R N hN B outputs x ab adv c M q charged priv qry addr core v world random) :
    ¬ R0Z.FsAbortBounds.CollEv M priv addr (core v world random) :=
  fun event => good (Or.inr (Or.inr event))

#print axioms off_full_collision
end R1Z.PV_OptB_Charged
