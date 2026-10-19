import AspisR1WithdrawalCaller.Types
open Aeneas Aeneas.Std
namespace WithdrawalCallerKindAudit
open AspisR1WithdrawalCaller.pool_v1.historical_anchor
#print PoolV1TransitionKind.read_discriminant
theorem privateTransfer : read_discriminant PoolV1TransitionKind.PrivateTransfer = 1#u8 := rfl
theorem withdrawal : read_discriminant PoolV1TransitionKind.Withdrawal = 2#u8 := rfl
#print axioms privateTransfer
#print axioms withdrawal
end WithdrawalCallerKindAudit
