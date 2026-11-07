import NLX_COMBINED_IMPORT
import NNF_TAS
set_option autoImplicit false
-- Focused combined import; inherited ledger roots are not re-audited here.
#print NNF_Folds.process_tx1
#print NNF_Folds.process_tx2
#print NNF_Folds.entry_tx1
#print NNF_Folds.entry_tx2
#print NNF_TAS.install
#print NNF_TAS.roots
#print NNF_TAS.weak_entry
#print axioms NNF_Folds.process_tx1
#print axioms NNF_Folds.process_tx2
#print axioms NNF_Folds.entry_tx1
#print axioms NNF_Folds.entry_tx2
#print axioms NNF_TAS.roots
#print axioms NNF_TAS.weak_entry
