import PV_STX_World
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_STX_NonceWorld
open Aeneas Aeneas.Std ProverRwFull PV_STX_Machine PV_STX_World
open PV_RJ4IDB (Bytes NativeEvent)
variable [ExternalTypes]
structure Delivery (A : Type) where
  answer : Answer A
  delivered : Bytes
  errorBytes : Option Bytes
  createdMode : Option Nat := none
structure Answers where
  pathOf : std.fs.File → Bytes
  bytesOf : Slice U8 → Bytes
  writeAll : World → std.fs.File → Slice U8 →
    Delivery ((core.result.Result Unit std.io.error.Error) × std.fs.File)
  sync : World → std.fs.File → Delivery (core.result.Result Unit std.io.error.Error)
  openReply : {P : Type} → core.convert.AsRef P std.path.Path → P → World →
    Bytes × Delivery (core.result.Result std.fs.File std.io.error.Error)
  optionsOpen : {P : Type} → core.convert.AsRef P std.path.Path →
    std.fs.OpenOptions → P → World →
    Bytes × Delivery (core.result.Result std.fs.File std.io.error.Error)

def errors (path : Bytes) (message : Option Bytes) : List NativeEvent :=
  match message with | none => [] | some b => [.otherFile (.failed path b)]

inductive Request : Type → Type 1 where
  | writeAll (file : std.fs.File) (bytes : Slice U8) :
      Request ((core.result.Result Unit std.io.error.Error) × std.fs.File)
  | sync (file : std.fs.File) : Request (core.result.Result Unit std.io.error.Error)
  | openFile {P : Type} (convert : core.convert.AsRef P std.path.Path) (path : P) :
      Request (core.result.Result std.fs.File std.io.error.Error)
  | optionsOpen {P : Type} (convert : core.convert.AsRef P std.path.Path)
      (options : std.fs.OpenOptions) (path : P) :
      Request (core.result.Result std.fs.File std.io.error.Error)

/-- Port of evh nonce primitives. The partial delivered prefix is retained
on all outcomes; a pending write must provide only NEW delivered bytes on each
poll. That is a provider protocol, not an atomic-write or success premise. -/
def writeAll (a : Answers) (file : std.fs.File) (bytes : Slice U8) (w : World) :
    Reply World NativeEvent ((core.result.Result Unit std.io.error.Error) × std.fs.File) :=
  let r := a.writeAll w file bytes
  let path := a.pathOf file
  ⟨r.answer,deliveredState path r.delivered w,
    [side "nonce-write-request" path,
     .otherFile (.write path (a.bytesOf bytes) r.delivered)] ++ errors path r.errorBytes⟩

def sync (a : Answers) (file : std.fs.File) (w : World) :
    Reply World NativeEvent (core.result.Result Unit std.io.error.Error) :=
  let r := a.sync w file
  let path := a.pathOf file
  match r.answer with
  | .returned (.ok (.Ok ())) =>
    ⟨r.answer,syncedState path w,
      [side "nonce-sync-request" path,.otherFile (.sync path)] ++ errors path r.errorBytes⟩
  | _ => ⟨r.answer,w,[side "nonce-sync-request" path] ++ errors path r.errorBytes⟩

def openFile {P : Type} (a : Answers) (convert : core.convert.AsRef P std.path.Path)
    (path : P) (w : World) : Reply World NativeEvent (core.result.Result std.fs.File std.io.error.Error) :=
  let r := a.openReply convert path w
  ⟨r.2.answer,w,[side "nonce-open-request" r.1] ++ errors r.1 r.2.errorBytes⟩

def optionsOpen {P : Type} (a : Answers) (convert : core.convert.AsRef P std.path.Path)
    (options : std.fs.OpenOptions) (path : P) (w : World) :
    Reply World NativeEvent (core.result.Result std.fs.File std.io.error.Error) :=
  let r := a.optionsOpen convert options path w
  let requestEvents := [side "nonce-options-open-request" r.1]
  match r.2.answer,r.2.createdMode with
  | .returned (.ok (.Ok _)),some mode =>
    ⟨r.2.answer,deliveredState r.1 [] w,
      requestEvents ++ [.otherFile (.create r.1 mode)] ++ errors r.1 r.2.errorBytes⟩
  | _,_ => ⟨r.2.answer,w,requestEvents ++ errors r.1 r.2.errorBytes⟩

def handler (a : Answers) : Handler Request World NativeEvent := fun op w =>
  match op with
  | .writeAll file bytes => writeAll a file bytes w
  | .sync file => sync a file w
  | .openFile convert path => openFile a convert path w
  | .optionsOpen convert options path => optionsOpen a convert options path w

/-- Native I/O failure does not roll back the file prefix, including panic
and abort answers. No completed helper run appears in this statement. -/
theorem write_prefix (a : Answers) (file : std.fs.File) (bytes : Slice U8) (w : World) :
    (writeAll a file bytes w).world = deliveredState (a.pathOf file) (a.writeAll w file bytes).delivered w ∧
    (writeAll a file bytes w).answer = (a.writeAll w file bytes).answer := ⟨rfl,rfl⟩

theorem failed_sync_frame (a : Answers) (file : std.fs.File) (w : World)
    (e : std.io.error.Error) (h : (a.sync w file).answer = .returned (.ok (.Err e))) :
    (sync a file w).world = w := by simp only [sync,h]

#print axioms write_prefix
#print axioms failed_sync_frame
end PV_STX_NonceWorld
