import ClaimsUnrolledParentTypes
set_option autoImplicit false
namespace NFN_ReserveOwner
abbrev ReserveError := AspisR1ClaimsUnrolledParent.alloc.collections.TryReserveError
theorem error_owner : ReserveError = AspisR1ClaimsUnrolledParent.alloc.collections.TryReserveError := rfl
#print axioms error_owner
end NFN_ReserveOwner
