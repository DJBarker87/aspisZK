import R1Z.GamesR1PBin
import R1Z.SimCostReplay

/-! Full ideal-game erasure through an abstract preparation stage. The stage
instance is intentionally an explicit residual, never fabricated by attaching
a budget to an unevaluated mathematical function. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostIdeal
open R0P R0Z.JointView R0Z.FsStatement R0Z.FsAbort R1Z.Batched
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.SimCostWriter R1Z.SimCostReplay
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

structure Prepared (K CommitHandle Aux : Type) [Field K] where
  view : View K CommitHandle Aux R1Bat
  table : Table
  fallback : List UInt8 → OracleAnswer

variable (W : R1Wire K CommitHandle Aux) (N : Nat) (hN : 0 < N)
  (P : Challenges K → Prop) (x : Statement K CommitHandle)
  (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
abbrev Coins := (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)

def prepare (r : Coins (F := F) W N) : Prepared K CommitHandle Aux :=
  let H := W.look (r.1 ⟨0,hN⟩).2.2.2
  match firstGood (fun c => P (drawW W c)) r.1 with
  | none => ⟨W.failView, [], H⟩
  | some k =>
    let v := sim (drawW W (r.1 k)) (r.2 k)
    ⟨v, verLog W x v (r.1 k), H⟩

def finish (adv : R1Adv K CommitHandle Aux) (s : Prepared K CommitHandle Aux) :
    Costed (ROMView K CommitHandle Aux R1Bat) :=
  let r := programmed s.table s.fallback (adv.prog s.view s.table) W.qmax
  (⟨s.view, s.table ++ r.1⟩, r.2+s.table.length+1)

def finishRef (adv : R1Adv K CommitHandle Aux) (s : Prepared K CommitHandle Aux) :
    ROMView K CommitHandle Aux R1Bat :=
  ⟨s.view, s.table ++ runLog (adv.prog s.view s.table)
    (fun a => (s.table.lookup a).getD (s.fallback a)) W.qmax⟩

theorem finish_erase (adv : R1Adv K CommitHandle Aux) (s : Prepared K CommitHandle Aux) :
    (finish W adv s).1 = finishRef W adv s := by
  simp only [finish, finishRef, programmed_erase]

theorem ideal_reference (Pr : R1ProverP K CommitHandle Aux F W)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (adv : R1Adv K CommitHandle Aux) (r : Coins (F := F) W N) :
    finishRef W adv (prepare W N hN P x sim r) =
      (fsR1P W Pr N hN P Vp).ideal sim adv x r := by
  change _ = retryOut N (fun c => P (drawW W c)) (fun c t => sim (drawW W c) t) _ _ r
  unfold retryOut prepare
  cases hh : firstGood (fun c => P (drawW W c)) r.1 with
  | none => simp only [hh, finishRef, abR1, List.nil_append, List.lookup_nil, Option.getD_none]
  | some k =>
    simp only [hh, finishRef, abR1]
    have hor : (fun a => ((verLog W x (sim (drawW W (r.1 k)) (r.2 k)) (r.1 k)).lookup a).getD
        (W.look (r.1 ⟨0,hN⟩).2.2.2 a)) =
        progOracle W x (sim (drawW W (r.1 k)) (r.2 k)) (r.1 k) (r.1 ⟨0,hN⟩).2.2.2 := by
      funext a
      unfold progOracle
      cases (verLog W x (sim (drawW W (r.1 k)) (r.2 k)) (r.1 k)).lookup a <;> rfl
    rw [hor]

/-- Every prelude computation is included in the stage: uniform samples,
public predicate checks for at most N attempts, simE field expressions,
metadata, encoding and verifier-log construction. Its concrete implementation
and bound are not yet supplied by the statistical privacy development. -/
abbrev Preparation (C : Nat) := Stage (prepare W N hN P x sim) C

def run (C : Nat) (prep : Preparation W N hN P x sim C)
    (adv : R1Adv K CommitHandle Aux) (r : Coins (F := F) W N) :
    Costed (ROMView K CommitHandle Aux R1Bat) :=
  bind (prep.run r) (finish W adv)

theorem run_erase (Pr : R1ProverP K CommitHandle Aux F W)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (C : Nat) (prep : Preparation W N hN P x sim C)
    (adv : R1Adv K CommitHandle Aux) (r : Coins (F := F) W N) :
    (run W N hN P x sim C prep adv r).1 = (fsR1P W Pr N hN P Vp).ideal sim adv x r := by
  rw [run, erase_bind, finish_erase, prep.erase]
  exact ideal_reference W N hN P x sim Pr Vp adv r

/-- Explicit size/encoding obligations; none follows merely from q queries. -/
def Sizes (L T : Nat) (adv : R1Adv K CommitHandle Aux) (s : Prepared K CommitHandle Aux) : Prop :=
  s.table.length ≤ T ∧ KeysBound L s.table ∧
    AddressBound (fun a => (s.table.lookup a).getD (s.fallback a)) L
      (adv.prog s.view s.table) W.qmax

def coefficient (C L T : Nat) : Nat := C+(T+1)*(2*L+3)+3*T+4

theorem run_linear (C L T : Nat) (prep : Preparation W N hN P x sim C)
    (adv : R1Adv K CommitHandle Aux) (r : Coins (F := F) W N)
    (hs : Sizes W L T adv (prepare W N hN P x sim r)) :
    (run W N hN P x sim C prep adv r).2 ≤ coefficient C L T*(W.qmax+1) := by
  have hv := prep.erase r
  have hb := prep.bound r
  have ht : Sizes W L T adv (prep.run r).1 := by rw [hv]; exact hs
  obtain ⟨hlen,hkeys,haddr⟩ := ht
  have hr := programmed_linear (prep.run r).1.table (prep.run r).1.fallback
    (adv.prog (prep.run r).1.view (prep.run r).1.table) W.qmax L hkeys haddr
  have hc : ((prep.run r).1.table.length+1)*(2*L+3)+2*(prep.run r).1.table.length+3 ≤
      (T+1)*(2*L+3)+2*T+3 := by nlinarith
  have hm := Nat.mul_le_mul_right (W.qmax+1) hc
  change (prep.run r).2 + ((programmed _ _ _ _).2 + (prep.run r).1.table.length+1) ≤ _
  unfold coefficient
  nlinarith

#print axioms finish_erase
#print axioms ideal_reference
#print axioms run_erase
#print axioms run_linear
end R1Z.SimCostIdeal
