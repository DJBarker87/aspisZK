module
import all Lean.Shell
namespace NFO_MemoryLimit
public def set : BaseIO Unit := Lean.Internal.setMaxMemory (7000 * 1024 * 1024)
end NFO_MemoryLimit
