import R1Z.PV_OWNC_FoldSource
set_option autoImplicit false
namespace R1Z.PV_OWNC_Specialization
/-- Const selection in deployed in_place_collect.rs. Filter is non-expanding
(merge=expand=1), Link is non-ZST, and source/destination layouts coincide. -/
def collectible (srcSize dstSize srcAlign dstAlign merge expand : Nat) : Bool :=
 srcSize != 0 && dstSize != 0 && srcAlign==dstAlign && srcSize*merge>=dstSize*expand

def needsRealloc (srcSize dstSize srcAlign dstAlign srcCap dstCap : Nat) : Bool :=
 if srcAlign != dstAlign then true
 else if dstSize != 0 && srcSize%dstSize==0 then false
 else srcCap>0 && srcCap*srcSize != dstCap*dstSize

theorem selected : collectible 8 8 2 2 1 1=true := by decide

theorem no_shrink (cap : Nat) : needsRealloc 8 8 2 2 cap cap=false := rfl

theorem capacity_bytes (cap : Nat) : cap*8/8=cap := by omega
#print axioms selected
#print axioms no_shrink
#print axioms capacity_bytes
end R1Z.PV_OWNC_Specialization
