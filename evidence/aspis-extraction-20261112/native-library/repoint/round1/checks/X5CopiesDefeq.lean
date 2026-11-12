import AspisFailureBoundModel
import BinHonestQueryBudget
/-! X5 side check (tool, nothing proved and nothing added to the chain): each replaced definition is the
original by `rfl` in the AFTER environment, where both are loaded. -/
example : @AspisR1.AspisLib.OraclePortAdmission.Guard = @AspisR1.OraclePortAdmission.Guard := rfl
example : @AspisR1.AspisLib.RecordedBinaryExperimentBin.dec = @AspisR1.RecordedBinaryExperimentBin.dec := rfl
example : @AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision = @AspisR1.RecordedBinaryExperimentBin.binaryCollision := rfl
example : @AspisR1.AspisLib.DecoderQueryAccounting.AdversaryQueries = @AspisR1.DecoderQueryAccounting.AdversaryQueries := rfl
example : @AspisHonestBudgetBase.raw = @AspisR1.BinHonestQueryBudget.raw := rfl
