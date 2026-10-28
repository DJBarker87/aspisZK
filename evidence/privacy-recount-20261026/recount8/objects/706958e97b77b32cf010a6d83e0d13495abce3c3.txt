import R1Z.PDict_FinalDictionary
import R1Z.PDict_SHAConstructorSource
import R1Z.PDict_PathRefSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Publication
open Aeneas Aeneas.Std ProverRwFull
abbrev native := PDict_FinalDictionary.native
abbrev shaNew := PDict_CryptoTypes.sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new

/-- Extends the simultaneous dictionary with extracted pure std identity and
SHA constructor. Both IVs are definitions from actual constants-inclusive
extraction; neither is an external constant assumption. -/
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_FinalDictionary.selected base ops with
    op27 := PDict_PathTypes.std.path.Path.Insts.CoreConvertAsRefPath.as_ref
    op206 := shaNew }

theorem op27_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (path : PDict_PathTypes.std.path.Path) :
    (selected base ops).op27 path = .ok path := rfl

theorem op206_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (size : Usize) :
    (selected base ops).op206 size = shaNew size := rfl

theorem sha224 : shaNew 28#usize = .ok (.Ok
    { state := PDict_CryptoTypes.sha2.consts.H256_224, block_len := 0#u64 }) := rfl

theorem sha256 : shaNew 32#usize = .ok (.Ok
    { state := PDict_CryptoTypes.sha2.consts.H256_256, block_len := 0#u64 }) := rfl

theorem sha_reject (size : Usize) (h28 : size.val ≠ 28) (h32 : size.val ≠ 32) :
    shaNew size = .ok (.Err ()) := by
  simp only [shaNew, PDict_CryptoTypes.sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new]

#print axioms op27_installed
#print axioms op206_installed
#print axioms sha224
#print axioms sha256
#print axioms sha_reject
end R1Z.PDict_Publication
