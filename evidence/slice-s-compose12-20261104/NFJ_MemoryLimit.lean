module
import all Lean.Shell
namespace NFJ_MemoryLimit
public def set : BaseIO Unit := Lean.Internal.setMaxMemory (7000 * 1024 * 1024)
end NFJ_MemoryLimit
