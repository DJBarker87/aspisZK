-- Body retained from aeneas-source-path-owned-opt-focused-01.
-- The generated template's PathBuf type is resolved to the existing frozen
-- ExternalTypes carrier. No generated template axiom is imported.
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
namespace PV_CBL_PathOwnedReference

def path_owned_reference (base : ProverRwFull.ExternalTypes)
    (p : @ProverRwFull.std.path.PathBuf base) :
    Result (@ProverRwFull.std.path.PathBuf base) := do
  ok p
#print axioms path_owned_reference
end PV_CBL_PathOwnedReference
