import R1Z.PDict_FormatterQuotient244
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FileWorld244
open Aeneas Aeneas.Std ProverRwFull

/-- File::flush is the already-proved pure Unix no-op. Its world lift consumes
no event and introduces no environmental flush law or availability premise. -/
def flush [ExternalTypes] {E : Type} (file : std.fs.File)
    (world : PDict_World244.World E) :
    Result (((core.result.Result Unit std.io.error.Error) × std.fs.File) ×
      PDict_World244.World E) := do
  let result ← PDict_FileFlush.flush file
  .ok (result,world)

theorem flush_source [ExternalTypes] {E : Type} (file : std.fs.File)
    (world : PDict_World244.World E) :
    flush file world = .ok ((.Ok (),file),world) := rfl

/-- Borrowing an error observation for kind does not modify payload identity,
message bytes, or either world cursor. Its native projection remains subject
to the pure native evidence, rather than an assumed syscall replacement. -/
def kind {E : Type} (error : PDict_World244.Error) (world : PDict_World244.World E) :
    Result (core.io.error.ErrorKind × PDict_World244.World E) := .ok (PDict_World244.Error.kind error,world)

theorem kind_source (base : ExternalTypes) (O S E : Type)
    (ops : @ExternalFuns (PDict_FormatterQuotient244.types base O S))
    (error : PDict_World244.Error) (world : PDict_World244.World E) :
    kind error world =
      (do let result ← (PDict_FormatterQuotient244.selected base O S ops).op23 error
          .ok (result,world)) := rfl

#print axioms flush_source
#print axioms kind_source
end R1Z.PDict_FileWorld244
