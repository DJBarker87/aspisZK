module
public import NEP_Planted
noncomputable section
namespace PV_D595_Cases
public inductive Box where
  | mk : Nat → Box
private def secret : Nat := NEP_Planted.auxAx
public def payload : Box := Box.mk secret
public theorem proof : True := NEP_Planted.proof
end PV_D595_Cases
#print axioms PV_D595_Cases.payload
#print axioms PV_D595_Cases.proof
