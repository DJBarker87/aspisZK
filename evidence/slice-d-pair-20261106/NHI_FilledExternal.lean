import NHI_FilledTypes
set_option autoImplicit false
namespace NHI_FilledRef
abbrev alloc.collections.TryReserveError := FIo_Native.alloc.collections.TryReserveError
abbrev core.result.Result.map_err := @FIo_Native.core.result.Result.map_err
abbrev alloc.vec.Vec.try_reserve_exact := @FIo_Native.alloc.vec.Vec.try_reserve_exact
end NHI_FilledRef
