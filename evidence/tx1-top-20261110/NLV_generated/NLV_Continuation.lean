import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result NLJ_Tx1
open CheckpointBytes5Effect (Code)
def continuation (cfg : Configuration) : Post → Code Out
 | .inl out => pure out
 | .inr after => denote cfg after
end AspisR1.NLV_Tree
end
