module
import all Lean.Shell
namespace NFA_MemoryLimit
/-- The same 7000 MiB runtime threshold supplied by lean -M7000. -/
public def set : BaseIO Unit := Lean.Internal.setMaxMemory (7000 * 1024 * 1024)
end NFA_MemoryLimit
