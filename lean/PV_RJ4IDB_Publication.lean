import PV_RJ4IDB_ClientSuffix
set_option autoImplicit false
namespace PV_RJ4IDB
/-- runjoin owns publish_compact's proof equation. The produced proof is data,
not an assumption that the complete actual observation equals its decoder. -/
structure PublicationInput where
 afterstate : Bytes
 publish_compact : Bytes
 statement : Bytes
 proofPath : Bytes
 statementPath : Bytes

def proofBytes (p : PublicationInput) := p.afterstate ++ p.publish_compact
/-- These are REQUESTS. Delivery, file/open errors and cleanup come from the
native file operations; their traces are never replaced by these requests. -/
def requestedPublication (p : PublicationInput) : List Event :=
 [.file (.write p.proofPath (proofBytes p) []),
  .file (.write p.statementPath p.statement [])]

theorem proof_statement_order (p : PublicationInput) : files (requestedPublication p) =
 [.write p.proofPath (p.afterstate++p.publish_compact) [],
  .write p.statementPath p.statement []] := rfl

theorem publication_append_prefix (p : PublicationInput) (prefix : List Event) :
 files (prefix ++ requestedPublication p) = files prefix ++
 [.write p.proofPath (p.afterstate++p.publish_compact) [],
  .write p.statementPath p.statement []] := by
 rw [files_append,proof_statement_order]
#print axioms proof_statement_order
#print axioms publication_append_prefix
end PV_RJ4IDB
