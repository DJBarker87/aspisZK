import RPu_FJi_SumBlocks
import RPu_FJi_WidePack
import RPu_JFv_TX2_ScalarMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_HeadValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FJi_Accumulations
open FIo_FieldBridge (wide)
/-- Coordinate-only decoder identity; no concrete arithmetic is evaluated. -/
theorem packed (x : NE) : decodeWide (wide x)=FJi_WidePack.pack
    (fun j=>(JFv_TX2_ArrayMeaning.cell (JFv_TX2_FromLimbsMeaning.limbs x) j).val) := rfl

def model (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) : AspisWideTower.WideExact :=
  FJi_WidePack.pack (fun j=>(FJi_InnerStep.sum q g slot j.val 0 26 : FJi_WidePack.F))

/-- Full base-field prefix VALUE on the SAME selected powers/opening. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (limbs : Sums) (head : NE)
    (loopRun : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q g slot (Array.repeat 8#usize 0#u64)=ok limbs)
    (finish : JFs_TX2_DotSuffix.scalarFinish limbs=ok head) :
    decodeWide (wide head)=model q g slot := by
  have values := (FJi_OuterValue.value q g slot limbs loopRun).2
  rw [packed]
  apply congrArg FJi_WidePack.pack
  funext j
  rw [JFv_TX2_ScalarMeaning.value limbs head finish j,←FJi_OuterTerm.at_fin,values j,
    FJi_SumBlocks.source q g slot j.val 7 (by decide)]
  exact ZMod.natCast_mod _ _
#print axioms packed
#print axioms value
end AspisR1.FJi_HeadValue
end
