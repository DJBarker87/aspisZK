import R1Z.PV_RunJoin_FixtureRecords

/-! Explicit coordinate maps for spend data. These definitions work for an
arbitrary scalar function, including the base-coordinate projection. They
do not assert preservation of the spend equations by an arbitrary function. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SpendDataMap
open AspisR1

open R0P AspisPool.V7PairLeafOccupancy SpendRelation
variable {K L M : Type}

def digest (f : K → L) (d : R0P.Digest K) : R0P.Digest L := fun i => f (d i)

def path (f : K → L) (p : Fin 24 → Bool × R0P.Digest K) :
    Fin 24 → Bool × R0P.Digest L := fun i => ((p i).1, digest f (p i).2)

def pair (f : K → L) (p : PairLeaf K) : PairLeaf L :=
  { firstCommitment := digest f p.firstCommitment
    secondOccupied := f p.secondOccupied
    secondCommitment := digest f p.secondCommitment
    secondOccupancyInverse := f p.secondOccupancyInverse }

def witness (f : K → L) (w : Witness K) : Witness L :=
  { inputValue := w.inputValue
    outputValue := w.outputValue
    changeValue := w.changeValue
    sk := digest f w.sk
    salt := digest f w.salt
    path := path f w.path
    pair := pair f w.pair
    recipientOwner := digest f w.recipientOwner
    recipientSalt := digest f w.recipientSalt
    changeOwner := digest f w.changeOwner
    changeSalt := digest f w.changeSalt }

def mapPublic (f : K → L) (p : Public K) : Public L :=
  { variant := p.variant
    anchor := digest f p.anchor
    nullifier := digest f p.nullifier
    assetId := f p.assetId
    recipient := p.recipient.map (digest f)
    change := digest f p.change
    withdrawalAmount := p.withdrawalAmount.map f
    nextPairIndex := p.nextPairIndex
    snapshotFrontier := fun i => digest f (p.snapshotFrontier i)
    nextRoot := digest f p.nextRoot
    nextFrontier := fun i => digest f (p.nextFrontier i) }

theorem witness_id (w : Witness K) : witness id w = w := by
  cases w
  rfl

theorem witness_comp (f : K → L) (g : L → M) (w : Witness K) :
    witness g (witness f w) = witness (g ∘ f) w := by
  rfl

theorem mapPublic_id (p : Public K) : mapPublic id p = p := by
  rcases p with ⟨v, a, n, asset, recipient, change, amount, index, frontier, root, next⟩
  cases recipient <;> cases amount <;> rfl

theorem mapPublic_comp (f : K → L) (g : L → M) (p : Public K) :
    mapPublic g (mapPublic f p) = mapPublic (g ∘ f) p := by
  rcases p with ⟨v, a, n, asset, recipient, change, amount, index, frontier, root, next⟩
  cases recipient <;> cases amount <;> rfl

#print axioms witness_id
#print axioms witness_comp
#print axioms mapPublic_id
#print axioms mapPublic_comp
end R1Z.PV_RunJoin_SpendDataMap
