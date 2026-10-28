import NDO_JGk_TX2_FrontierOrder0
import NDO_JGk_TX2_FrontierOrder2
set_option autoImplicit false
namespace AspisR1.JGk_TX2_SiblingBase
open AspisV8R19.SourceDuplexStep
def native0 (h b : Nat) : State := JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes0
  (JGk_TX2_Group0_00.stream.idxOf (h,b))
def native1 (h b : Nat) : State := JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes1
  (JGk_TX2_Group0_00.stream.idxOf (h,b))
def native2 (h b : Nat) : State := JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes2
  (JGk_TX2_Group2_00.stream.idxOf (h,b))
end AspisR1.JGk_TX2_SiblingBase
