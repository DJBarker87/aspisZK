-- Canonical owner normalization of the identical reference-only error schema.
-- Original generated source and hashes are retained in NEC_OWNER_NORMALIZATION.json.
import NEC_Reference.Types
set_option autoImplicit false
namespace NEC_ReplyRef
abbrev ChildError (E : Type) := NEC_Reference.ChildError E
namespace ChildError
abbrev Child {E : Type} (error : E) : NEC_ReplyRef.ChildError E :=
 NEC_Reference.ChildError.Child error
end ChildError
end NEC_ReplyRef
