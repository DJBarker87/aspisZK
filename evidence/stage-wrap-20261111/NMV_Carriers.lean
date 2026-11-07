import NMV_Model
import S2W_ReturnedCheckpoint
set_option autoImplicit false
namespace NMV_Carriers
open Aeneas Aeneas.Std AdapterRw NMV_Model
abbrev CanonicalOwned := r1_pool_adapter.owned.OwnedAccount
abbrev CanonicalBytes := alloc.vec.Vec U8
abbrev CanonicalKey := solana_pubkey.Pubkey

def byte (b : U8) : UInt8 := AspisR1.S2W_ReturnedCheckpoint.nativeByte b
def bytes (b : CanonicalBytes) : Bytes := b.val.map byte
def key (b : CanonicalKey) : Bytes := b.val.map byte

theorem byte_injective : Function.Injective byte := by
 intro a b h
 apply UScalar.eq_of_val_eq
 have ha : (byte a).toNat=a.val := UInt8.toNat_ofNat_of_lt' a.bv.isLt
 have hb : (byte b).toNat=b.val := UInt8.toNat_ofNat_of_lt' b.bv.isLt
 exact ha.symm.trans ((congrArg UInt8.toNat h).trans hb)

theorem list_injective : Function.Injective (List.map byte) := by
 intro xs
 induction xs with
 | nil =>
   intro ys h
   cases ys with
   | nil => rfl
   | cons y ys => cases h
 | cons x xs ih =>
   intro ys h
   cases ys with
   | nil => cases h
   | cons y ys =>
     have head : x=y := byte_injective (List.cons.inj h).1
     have tail : xs=ys := ih (List.cons.inj h).2
     cases head; cases tail; rfl

theorem bytes_injective : Function.Injective bytes := by
 intro a b h
 rcases a with ⟨av,ah⟩
 rcases b with ⟨bv,bh⟩
 have same : av=bv := list_injective h
 subst bv
 rfl

theorem key_injective : Function.Injective key := by
 intro a b h
 rcases a with ⟨av,ah⟩
 rcases b with ⟨bv,bh⟩
 have same : av=bv := list_injective h
 subst bv
 rfl

def lengthView : core.result.Result Usize PE → Except PE Nat
 | .Ok n => .ok n.val
 | .Err e => .error e

def bytesView : core.result.Result CanonicalBytes PE → Except PE Bytes
 | .Ok b => .ok (bytes b)
 | .Err e => .error e

theorem length_injective : Function.Injective lengthView := by
 intro a b h
 cases a with
 | Err a => cases b with
   | Err b => cases h; rfl
   | Ok b => cases h
 | Ok a => cases b with
   | Err b => cases h
   | Ok b =>
     have eq : a.val=b.val := Except.ok.inj h
     have same : a=b := UScalar.eq_of_val_eq eq
     cases same; rfl

theorem bytesView_injective : Function.Injective bytesView := by
 intro a b h
 cases a with
 | Err a => cases b with
   | Err b => cases h; rfl
   | Ok b => cases h
 | Ok a => cases b with
   | Err b => cases h
   | Ok b =>
     have same : a=b := bytes_injective (Except.ok.inj h)
     cases same; rfl

/-- A full observation keeps BOTH deferred error fields and all metadata.
No arbitrary ProgramError constructor is collapsed into a Boolean or tag. -/
structure View where
 key : Bytes
 owner : Bytes
 signer : Bool
 writable : Bool
 executable : Bool
 length : Except PE Nat
 bytes : Except PE Bytes

def canonical (a : CanonicalOwned) : View :=
 ⟨key a.key,key a.owner,a.is_signer,a.is_writable,a.executable,
   lengthView a.length,bytesView a.bytes⟩

theorem canonical_injective : Function.Injective canonical := by
 intro a b h
 have hk : a.key=b.key := key_injective (congrArg View.key h)
 have ho : a.owner=b.owner := key_injective (congrArg View.owner h)
 have hs : a.is_signer=b.is_signer := congrArg View.signer h
 have hw : a.is_writable=b.is_writable := congrArg View.writable h
 have he : a.executable=b.executable := congrArg View.executable h
 have hl : a.length=b.length := length_injective (congrArg View.length h)
 have hb : a.bytes=b.bytes := bytesView_injective (congrArg View.bytes h)
 cases a
 cases b
 cases hk; cases ho; cases hs; cases hw; cases he; cases hl; cases hb
 rfl

/-- Snapshot's only two generated error values; other child ProgramErrors
remain full PE values in every Outcome and are never mapped through this. -/
def snapshotError : NMV_Snapshot.Error → PE
 | .borrow => .AccountBorrowFailed
 | .invalidData => .InvalidAccountData

def native (a : NMV_Snapshot.Owned) : View :=
 ⟨a.key,a.owner,a.signer,a.writable,a.executable,
  a.length.mapError snapshotError,a.bytes.mapError snapshotError⟩

def Related (a : NMV_Snapshot.Owned) (b : CanonicalOwned) : Prop := native a=canonical b

#print axioms canonical_injective
#print axioms byte_injective
#print axioms list_injective
#print axioms bytes_injective
#print axioms key_injective
#print axioms length_injective
#print axioms bytesView_injective
end NMV_Carriers
