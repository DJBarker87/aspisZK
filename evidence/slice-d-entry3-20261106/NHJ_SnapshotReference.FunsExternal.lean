import Aeneas
import NHJ_SnapshotReference.Types
namespace NHJ_SnapshotReference
open Aeneas Aeneas.Std
/-- This branch is unreachable on BorrowErrorLaw (the sole error is ABF).
No claim about native String cloning is exported or used. -/
def alloc.string.String.Insts.CoreCloneClone.clone (_ : String) : Result String := .div
end NHJ_SnapshotReference
