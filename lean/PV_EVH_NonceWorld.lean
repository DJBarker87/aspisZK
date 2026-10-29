import PV_EVH_Entropy
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonceWorld
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_Entropy
open PV_RJ4IDB (Bytes NativeEvent)
variable [ExternalTypes]

structure Delivery (A : Type) where
  result : Result A
  delivered : Bytes
  errorBytes : Option Bytes

/-- Typed boundary data, with no supplied event trace. The adapter's path,
delivery and errno fidelity remains an observation/rdea-1 obligation. -/
structure Answers where
  pathOf : std.fs.File → Bytes
  bytesOf : Slice U8 → Bytes
  writeAll : World → std.fs.File → Slice U8 →
    Delivery ((core.result.Result Unit std.io.error.Error) × std.fs.File)
  sync : World → std.fs.File → Delivery (core.result.Result Unit std.io.error.Error)
  open : {P : Type} → core.convert.AsRef P std.path.Path → P → World →
    Bytes × Delivery (core.result.Result std.fs.File std.io.error.Error)
  optionsOpen : {P : Type} → core.convert.AsRef P std.path.Path →
    std.fs.OpenOptions → P → World →
    Bytes × Delivery (core.result.Result std.fs.File std.io.error.Error)

def deliveredState (path bytes : Bytes) (w : World) : World :=
  if w.files.any (fun f => f.path == path) then
    {w with files := w.files.map (fun f =>
      if f.path == path then {f with delivered := f.delivered ++ bytes} else f)}
  else {w with files := w.files ++ [⟨path,bytes,[]⟩]}

def syncedState (path : Bytes) (w : World) : World :=
  {w with files := w.files.map (fun f =>
    if f.path == path then {f with durable := f.delivered} else f)}

def errors (path : Bytes) (message : Option Bytes) : List NativeEvent :=
  match message with
  | none => []
  | some b => [.otherFile (.failed path b)]

/-- The partial delivered prefix survives .Err, panic and divergence answers.
Whether a particular runtime outcome permits a delivery is an explicit
boundary fidelity obligation, not an assumption of atomic writes. -/
def writeAll (a : Answers) (file : std.fs.File) (bytes : Slice U8) :
    M ((core.result.Result Unit std.io.error.Error) × std.fs.File) := fun w =>
  let r := a.writeAll w file bytes
  let path := a.pathOf file
  ⟨r.result,deliveredState path r.delivered w,
    [.side (ascii "nonce-write-request") path,
     .otherFile (.write path (a.bytesOf bytes) r.delivered)] ++ errors path r.errorBytes⟩

def sync (a : Answers) (file : std.fs.File) :
    M (core.result.Result Unit std.io.error.Error) := fun w =>
  let r := a.sync w file
  let path := a.pathOf file
  match r.result with
  | .ok (.Ok ()) =>
      ⟨r.result,syncedState path w,
        [.side (ascii "nonce-sync-request") path,.otherFile (.sync path)] ++ errors path r.errorBytes⟩
  | _ => ⟨r.result,w,[.side (ascii "nonce-sync-request") path] ++ errors path r.errorBytes⟩

def openFile {P : Type} (a : Answers) (convert : core.convert.AsRef P std.path.Path)
    (path : P) : M (core.result.Result std.fs.File std.io.error.Error) := fun w =>
  let r := a.open convert path w
  ⟨r.2.result,w,[.side (ascii "nonce-open-request") r.1] ++ errors r.1 r.2.errorBytes⟩

/-- Whether create_new succeeded is exposed through the typed answer. The
create mode is supplied from the actual options adapter, not guessed here. -/
def optionsOpen {P : Type} (a : Answers) (convert : core.convert.AsRef P std.path.Path)
    (options : std.fs.OpenOptions) (path : P) :
    M (core.result.Result std.fs.File std.io.error.Error) := fun w =>
  let r := a.optionsOpen convert options path w
  ⟨r.2.result,w,[.side (ascii "nonce-options-open-request") r.1] ++ errors r.1 r.2.errorBytes⟩

variable [ExternalFuns]

theorem write_fixed (a : Answers) (file : std.fs.File) (bytes : Slice U8)
    (h : ∀ w, (a.writeAll w file bytes).result = std.fs.File.Insts.StdIoWrite.write_all file bytes) :
    FixedView (writeAll a file bytes) (std.fs.File.Insts.StdIoWrite.write_all file bytes) := h

theorem sync_fixed (a : Answers) (file : std.fs.File)
    (h : ∀ w, (a.sync w file).result = std.fs.File.sync_all file) :
    FixedView (sync a file) (std.fs.File.sync_all file) := by
  intro w
  unfold sync
  split <;> exact h w

theorem open_fixed {P : Type} (a : Answers) (convert : core.convert.AsRef P std.path.Path)
    (path : P) (h : ∀ w, (a.open convert path w).2.result = std.fs.File.open convert path) :
    FixedView (openFile a convert path) (std.fs.File.open convert path) := h

theorem options_fixed {P : Type} (a : Answers) (convert : core.convert.AsRef P std.path.Path)
    (options : std.fs.OpenOptions) (path : P)
    (h : ∀ w, (a.optionsOpen convert options path w).2.result = std.fs.OpenOptions.open convert options path) :
    FixedView (optionsOpen a convert options path) (std.fs.OpenOptions.open convert options path) := h

theorem write_prefix (a : Answers) (file : std.fs.File) (bytes : Slice U8) (w : World) :
    (writeAll a file bytes w).events =
      [.side (ascii "nonce-write-request") (a.pathOf file),
       .otherFile (.write (a.pathOf file) (a.bytesOf bytes) (a.writeAll w file bytes).delivered)] ++
        errors (a.pathOf file) (a.writeAll w file bytes).errorBytes := rfl

#print axioms write_fixed
#print axioms sync_fixed
#print axioms open_fixed
#print axioms options_fixed
#print axioms write_prefix
end PV_EVH_NonceWorld
