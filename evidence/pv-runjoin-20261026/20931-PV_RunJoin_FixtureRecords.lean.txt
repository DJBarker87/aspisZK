import R1Z.BuilderCanonical

/-! Mathematical records with the literal public fixture witness constants
from r0_fixture.rs / v7_pair_forest_fixture.rs. The native record/byte mapping
is a separate obligation. Hashes stay symbolic throughout this module. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureRecords
open R0P AspisR1 AspisR1.SpendRelation AspisPool.V7PairLeafOccupancy
abbrev M := R1J.SpendWitnessMap.F

def digest (seed : Nat) : R0P.Digest M := fun i => (seed + 17*i.val + 1 : Nat)

def path : Fin 24 → Bool × R0P.Digest M := fun i =>
  if i.val = 0 then (false,digest 900)
  else if i.val < 21 then
    (decide (((0x54321 : Nat) >>> (i.val-1)) &&& 1 = 1),digest (2000 + 20*(i.val-1)))
  else (decide (i.val ≠ 22),digest (3000 + 100*(i.val-21)))

def pair : PairLeaf M where
  firstCommitment := noteCommitment (ownerKey (digest 10)) 1000 77 (digest 100)
  secondOccupied := 1
  secondCommitment := digest 900
  secondOccupancyInverse := (digest 900 7)⁻¹

def witness (withdrawal : Bool) : Wspend where
  inputValue := ⟨1000,by decide⟩
  outputValue := if withdrawal then ⟨250,by decide⟩ else ⟨600,by decide⟩
  changeValue := if withdrawal then ⟨750,by decide⟩ else ⟨400,by decide⟩
  sk := digest 10
  salt := digest 100
  path := path
  pair := pair
  recipientOwner := digest 300
  recipientSalt := digest 400
  changeOwner := if withdrawal then digest 700 else digest 500
  changeSalt := if withdrawal then digest 800 else digest 600

def base (withdrawal : Bool) : Public M where
  variant := if withdrawal then .withdrawal else .privateTransfer
  anchor := merkleRoot (noteCommitment (ownerKey (digest 10)) 1000 77 (digest 100)) path
  nullifier := nullifierHash (digest 10) (digest 100)
  assetId := 77
  recipient := if withdrawal then none else some
    (noteCommitment (witness withdrawal).recipientOwner (witness withdrawal).outputValue.val
      77 (witness withdrawal).recipientSalt)
  change := noteCommitment (witness withdrawal).changeOwner (witness withdrawal).changeValue.val
    77 (witness withdrawal).changeSalt
  withdrawalAmount := if withdrawal then some 250 else none
  nextPairIndex := 0
  snapshotFrontier := fun i => AppendNode.frozenEmpty i.castSucc
  nextRoot := fun _ => 0
  nextFrontier := fun i => AppendNode.frozenEmpty i.castSucc

def outputPair (withdrawal : Bool) : R0P.Digest M :=
  if withdrawal then nodeCompress (base withdrawal).change (fun _ => 0)
  else nodeCompress (noteCommitment (witness withdrawal).recipientOwner
    (witness withdrawal).outputValue.val 77 (witness withdrawal).recipientSalt)
    (base withdrawal).change

def attachAppend {K : Type} [Field K] (pub : Public K) (pair : R0P.Digest K) : Public K :=
  { pub with
    nextRoot := AppendPath.pathPrefix pub pair 20
    nextFrontier := fun l => if l.val = digestCarry pub.nextPairIndex then
      AppendPath.pathPrefix pub pair l.val else pub.snapshotFrontier l }

theorem prefix_seal {K : Type} [Field K] (pub : Public K) (pair leaf : R0P.Digest K)
    (n : Nat) :
    AppendPath.pathPrefix (attachAppend pub pair) leaf n = AppendPath.pathPrefix pub leaf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [AppendPath.pathPrefix]
    split
    · rw [ih]
      rfl
    · exact ih

theorem seal_append {K : Type} [Field K] [DecidableEq K]
    (pub : Public K) (pair : R0P.Digest K)
    (output : SpendRelation.outputPair pub = some pair) : AppendBinding (attachAppend pub pair) := by
  refine ⟨pair,?_,?_,?_⟩
  · exact output
  · exact (prefix_seal pub pair pair 20).symm
  · intro hc
    change (if digestCarry pub.nextPairIndex = digestCarry pub.nextPairIndex then
      AppendPath.pathPrefix pub pair (digestCarry pub.nextPairIndex) else _) = _
    rw [if_pos rfl,prefix_seal]
    rfl

def fixturePublic (withdrawal : Bool) : Public M := attachAppend (base withdrawal) (outputPair withdrawal)

theorem pair_valid : pair.Valid := by
  have sentinel : digest 900 7 ≠ 0 := by
    change (1020 : ZMod 2147483647) ≠ 0
    intro zero
    have values := congrArg (fun a : ZMod 2147483647 => a.val) zero
    change 1020 = 0 at values
    omega
  change 1*(1-1) = (0 : M) ∧ digest 900 7 * (digest 900 7)⁻¹ = 1 ∧
    (1-1)*(digest 900 7)⁻¹ = 0 ∧ ∀ lane, (1-1)*digest 900 lane = 0
  simp only [sub_self,mul_zero,zero_mul,mul_inv_cancel₀ sentinel,true_and,implies_true]

theorem input_relation (withdrawal : Bool) :
    InputWitnessCore.Relation (fixturePublic withdrawal) (witness withdrawal).inputValue.val
      (witness withdrawal).sk (witness withdrawal).salt
      (witness withdrawal).path (witness withdrawal).pair where
  valid := pair_valid
  spendable := rfl
  commitment := rfl
  sibling := rfl
  nullifier := rfl
  membership := rfl

theorem append (withdrawal : Bool) : AppendBinding (fixturePublic withdrawal) := by
  apply seal_append
  cases withdrawal <;> rfl

theorem spend (withdrawal : Bool) : Rspend (fixturePublic withdrawal) (witness withdrawal) := by
  refine ⟨?_,input_relation withdrawal,?_,rfl,?_,append withdrawal⟩
  · cases withdrawal
    · exact ⟨rfl,rfl⟩
    · refine ⟨rfl,rfl,?_⟩
      change (some (250 : M)) ≠ some 0
      simpa only [ne_eq,Option.some.injEq] using (show (250 : M) ≠ 0 by
        change (250 : ZMod 2147483647) ≠ 0
        intro zero
        have values := congrArg (fun a : ZMod 2147483647 => a.val) zero
        change 250 = 0 at values
        omega)
  · cases withdrawal <;> decide
  · cases withdrawal <;> rfl

theorem withdrawal_spendPlus : BuilderSpendRelation.RspendPlus (fixturePublic true) (witness true) := by
  refine ⟨spend true,?_⟩
  intro impossible
  cases impossible

/-- Transfer retains precisely the adopted D50 change-sentinel obligation;
no concrete Poseidon recurrence is unfolded to conceal that remaining check. -/
theorem transfer_spendPlus (sentinel : (fixturePublic false).change 7 ≠ 0) :
    BuilderSpendRelation.RspendPlus (fixturePublic false) (witness false) :=
  ⟨spend false,fun _ => sentinel⟩

#print axioms prefix_seal
#print axioms seal_append
#print axioms pair_valid
#print axioms input_relation
#print axioms append
#print axioms spend
#print axioms withdrawal_spendPlus
#print axioms transfer_spendPlus
end R1Z.PV_RunJoin_FixtureRecords
