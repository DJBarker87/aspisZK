import Hiq_PoolGuards
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolW_Store
open Aeneas Aeneas.Std Result

abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Bytes := List U8

/-- Physical account data and full untouched metadata. Public keys, not role
indices or independently supplied account buffers, identify this store. -/
structure Cell (Metadata : Type) where
  data : Bytes
  metadata : Metadata

abbrev Store (Metadata : Type) := Key → Cell Metadata

def put {M : Type} (store : Store M) (key : Key) (bytes : Bytes) : Store M :=
  fun address => if address = key then { store address with data := bytes } else store address

def copyBoth {M : Type} (store : Store M) (master checkpoint : Key)
    (masterImage checkpointImage : Bytes) : Store M :=
  put (put store checkpoint checkpointImage) master masterImage

theorem put_here {M : Type} (store : Store M) (key : Key) (bytes : Bytes) :
    (put store key bytes key).data = bytes := by simp [put]

theorem put_other {M : Type} (store : Store M) (key address : Key) (bytes : Bytes)
    (different : address ≠ key) :
    put store key bytes address = store address := by simp [put,different]

theorem metadata {M : Type} (store : Store M) (key address : Key) (bytes : Bytes) :
    (put store key bytes address).metadata = (store address).metadata := by
  simp only [put]
  split <;> rfl

theorem checkpoint_copy {M : Type} (store : Store M) (master checkpoint : Key)
    (masterImage checkpointImage : Bytes) (unique : checkpoint ≠ master) :
    (copyBoth store master checkpoint masterImage checkpointImage checkpoint).data = checkpointImage := by
  simp [copyBoth,put,unique]

theorem master_copy {M : Type} (store : Store M) (master checkpoint : Key)
    (masterImage checkpointImage : Bytes) :
    (copyBoth store master checkpoint masterImage checkpointImage master).data = masterImage := by
  simp [copyBoth,put]

theorem frame {M : Type} (store : Store M) (master checkpoint address : Key)
    (masterImage checkpointImage : Bytes) (notMaster : address ≠ master)
    (notCheckpoint : address ≠ checkpoint) :
    copyBoth store master checkpoint masterImage checkpointImage address = store address := by
  simp [copyBoth,put,notMaster,notCheckpoint]

theorem all_metadata {M : Type} (store : Store M) (master checkpoint address : Key)
    (masterImage checkpointImage : Bytes) :
    (copyBoth store master checkpoint masterImage checkpointImage address).metadata =
      (store address).metadata := by
  simp only [copyBoth,metadata]

#print axioms put_here
#print axioms put_other
#print axioms metadata
#print axioms checkpoint_copy
#print axioms master_copy
#print axioms frame
#print axioms all_metadata
end AspisR1.PoolW_Store
end
