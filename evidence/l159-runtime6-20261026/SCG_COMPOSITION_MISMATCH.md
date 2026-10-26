# Exact carriers and quantifiers at the proposed composition

Target not yet established. This is a statement audit, not a newly adopted
assumption or an independence theorem about the installed protocol.

1. DrvC_SourceEntry.same_program is equality of two standalone functions
   `Input -> Program Bytes State Bool`. Their TX2 input is reconstructed from
   TX1's public/proof and returned checkpoint. It is not an equality with
   `SCE_Experiment.account`, whose result carrier is `Outcome A` and whose TX2
   input is the response-selected account entry.
2. SCE_NativeAccepted.accepted has antecedents `called1` and `called2` for
   native wrappers at the response-selected entries in ONE H; its conclusion
   is `accepted (eval H account).2 = true`. The direction needed to apply the
   native cuts from CleanAccountTransport's sole acceptance antecedent is the
   reverse implication. That reverse theorem is not among (a), (b), (c).
   SCE's byte projection theorems identify the first submitted bytes on every
   outcome but do not invert native acceptance or install game clauses.
3. FGl_Join/F3X_Join accepts a standalone `Submission` and returns equality
   between `eval H installedSource` and `eval H F3_Model.verifier`, OR a
   collision in `Hiq_RecordedJoint (F3X_AccountPrior.program ... prior s)`.
   Neither disjunct mentions the original SCE account's log or its selector.
   Equality of those two source/model logs therefore does not, by itself,
   supply SCF_Recovery's physical/source frame and first-cut equations.
4. CleanAccountTransport quantifies over EVERY H on ONE fixed adversary and
   uses account success alone. Its definition has NO admission, native-success,
   checkpoint-game, bank-lineage, persistence-instance or H-indexed deployment
   guard. Rc7's retained game/admission/native observations concern supplied
   fixed e1/e2 at supplied H. Even SCE_ConditionalTop has those facts only at
   its supplied H while its runtime failure is a mean over all worlds.
   They cannot be silently generalized to the response-selected entries in
   another H. SCG_WorldQuantifiers checks the elementary quantifier distinction;
   it does not exhibit a full protocol counterexample.

Checked progress narrows these boundaries:

- SCG_FirstCode/SecondCode and FirstTraceLog/SecondTraceLog identify the two
  reified child code/logs, including rejection and duplicate reads. WrapperLog
  proves allocator/copy/cleanup add no reads once the reservation succeeds.
  OuterLog.flatten preserves exact ordered child concatenation.
- SCG_Composition consumes same-cut native acceptance into the frozen3 join,
  with its SOURCE collision recorder kept explicit.
- SCG_NativeAccount consumes the retained native/game laws through P2PPrime's
  alternative on the PHYSICAL account recorder; SCG_SharedNative binds the
  same response-selected entries to Hiq_ByteSelection.select, one fixed
  outcome-dependent selector. These remain pointwise native/game theorems.

The next required concrete proof is a joint accepted-account refinement in
all worlds of the actual deployed game: obtain the SAME native/source cuts
(or their ideal-world counterparts), derive checkpoint association, identify
the physical/source ordered sublog and the query-map projection, and transport
that collision event and the three executable recovery inputs. This is a
proof obligation, not proposed trust. Requiring it as a new CleanTransport
premise in SCG_Top would merely bundle the missing conclusion; no such top is
installed here. The current account accepted flag and arbitrary project/select
arguments must not be presented as already encoding all these guards.

The native-direction diagnostic does not exclude an alternate proof directly
from ideal wrapper acceptance: invert those wrappers, derive SAME ideal
source cuts, then establish the checkpoint association under a correctly
game-indexed experiment. That route still has to prove the physical/source
sublog, collision projection and recovery cuts. No theorem here says the
whole desired composition is mathematically impossible.
