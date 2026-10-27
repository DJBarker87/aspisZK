import R1Z.PV_CBL_GenericArrayPower
namespace R1Z.PV_CBL_GenericArraySizes
set_option autoImplicit false

theorem sha_output {T : Type} (v : PV_CBL_GenericArrayPower.Storage T 5) :
    (PV_CBL_GenericArrayPower.flatten 5 v).length=32 :=
  PV_CBL_GenericArrayPower.length 5 v

theorem sha_block {T : Type} (v : PV_CBL_GenericArrayPower.Storage T 6) :
    (PV_CBL_GenericArrayPower.flatten 6 v).length=64 :=
  PV_CBL_GenericArrayPower.length 6 v

#print axioms sha_output
#print axioms sha_block
end R1Z.PV_CBL_GenericArraySizes
