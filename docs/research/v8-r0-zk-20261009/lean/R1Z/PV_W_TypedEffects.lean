import R1Z.PV_W_SourceSyntax
import R1Z.PV_W_SyntaxMap
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_TypedEffects
open ProverRwFull PV_W_Syntax PV_W_SyntaxMap
open Aeneas.Std
variable [ExternalTypes]

/-- Selected file operations retain typed arguments, rather than requiring
an interpreter to inspect a function thunk or recover an argument from a
previously evaluated Result. Helpers remain explicit unresolved subprograms. -/
inductive Primitive : Type → Type 1 where
  | helper {A : Type} (op : PV_W_SourceSyntax.Op A) : Primitive A
  | fileOpen {P : Type} (convert : ExternalFuns → core.convert.AsRef P std.path.Path) (path : P) :
      Primitive (core.result.Result std.fs.File std.io.error.Error)
  | fileSync (file : std.fs.File) : Primitive (core.result.Result Unit std.io.error.Error)
  | optionsOpen {P : Type} (convert : ExternalFuns → core.convert.AsRef P std.path.Path)
      (options : std.fs.OpenOptions) (path : P) :
      Primitive (core.result.Result std.fs.File std.io.error.Error)
  | errorKind (error : std.io.error.Error) : Primitive core.io.error.ErrorKind
  | writeAll (file : std.fs.File) (bytes : Slice U8) :
      Primitive ((core.result.Result Unit std.io.error.Error) × std.fs.File)

def embed {A : Type} : Primitive A → PV_W_SourceSyntax.Op A
  | .helper op => op
  | .fileOpen convert path => ⟨"std.fs.File.open",fun dictionary =>
      letI : ExternalFuns := dictionary
      std.fs.File.open (convert dictionary) path⟩
  | .fileSync file => ⟨"std.fs.File.sync_all",fun dictionary =>
      letI : ExternalFuns := dictionary
      std.fs.File.sync_all file⟩
  | .optionsOpen convert options path => ⟨"std.fs.OpenOptions.open",fun dictionary =>
      letI : ExternalFuns := dictionary
      std.fs.OpenOptions.open (convert dictionary) options path⟩
  | .errorKind error => ⟨"std.io.error.Error.kind",fun dictionary =>
      letI : ExternalFuns := dictionary
      std.io.error.Error.kind error⟩
  | .writeAll file bytes => ⟨"std.fs.File.Insts.StdIoWrite.write_all",fun dictionary =>
      letI : ExternalFuns := dictionary
      std.fs.File.Insts.StdIoWrite.write_all file bytes⟩

abbrev P (A : Type) := Program Primitive Aeneas.Std.Error A
instance : Monad P where
  pure := Program.pure
  bind := thenDo

def perform {A : Type} (op : Primitive A) : P A := .call op .pure

def invoke {A : Type} (label : String)
    (f : ExternalFuns → Aeneas.Std.Result A) : P A := perform (.helper ⟨label,f⟩)

def erase {A : Type} (dictionary : ExternalFuns) (p : P A) : Aeneas.Std.Result A :=
  PV_W_SourceSyntax.erase dictionary (mapOps embed p)

theorem erase_bind {A B : Type} (dictionary : ExternalFuns)
    (p : P A) (k : A → P B) :
    erase dictionary (p >>= k) = Aeneas.Std.bind (erase dictionary p) (fun a => erase dictionary (k a)) := by
  change PV_W_SourceSyntax.erase dictionary (mapOps embed (thenDo p k)) = _
  rw [map_bind,PV_W_SourceSyntax.erase_thenDo]
  rfl

theorem erase_perform {A : Type} (dictionary : ExternalFuns) (op : Primitive A) :
    erase dictionary (perform op) = (embed op).source dictionary := by
  change PV_W_SourceSyntax.erase dictionary
    (PV_W_SourceSyntax.invoke (embed op).label (embed op).source) = _
  exact PV_W_SourceSyntax.erase_invoke dictionary _ _

theorem erase_invoke {A : Type} (dictionary : ExternalFuns) (label : String)
    (f : ExternalFuns → Aeneas.Std.Result A) : erase dictionary (invoke label f) = f dictionary :=
  erase_perform dictionary (.helper ⟨label,f⟩)

theorem erase_pure {A : Type} (dictionary : ExternalFuns) (a : A) :
    erase dictionary (pure a : P A) = .ok a := rfl

/-- World-indexed DATA for the selected operations. No generic native purity,
OS atomicity, crash persistence, or helper adequacy is smuggled into a law. -/
structure Algebra (W C E : Type) where
  helper : {A : Type} → PV_W_SourceSyntax.Op A → PV_W_Threading.M W C E A
  fileOpen : {P : Type} → (ExternalFuns → core.convert.AsRef P std.path.Path) → P →
    PV_W_Threading.M W C E (core.result.Result std.fs.File std.io.error.Error)
  fileSync : std.fs.File → PV_W_Threading.M W C E (core.result.Result Unit std.io.error.Error)
  optionsOpen : {P : Type} → (ExternalFuns → core.convert.AsRef P std.path.Path) → std.fs.OpenOptions → P →
    PV_W_Threading.M W C E (core.result.Result std.fs.File std.io.error.Error)
  errorKind : std.io.error.Error → PV_W_Threading.M W C E core.io.error.ErrorKind
  writeAll : std.fs.File → Slice U8 →
    PV_W_Threading.M W C E ((core.result.Result Unit std.io.error.Error) × std.fs.File)

def interpret {W C E : Type} (a : Algebra W C E) : Interpreter Primitive W C E
  | _, .helper op => a.helper op
  | _, .fileOpen convert path => a.fileOpen convert path
  | _, .fileSync file => a.fileSync file
  | _, .optionsOpen convert options path => a.optionsOpen convert options path
  | _, .errorKind error => a.errorKind error
  | _, .writeAll file bytes => a.writeAll file bytes

#print axioms erase_bind
#print axioms erase_perform
#print axioms erase_invoke
#print axioms erase_pure
end R1Z.PV_W_TypedEffects
