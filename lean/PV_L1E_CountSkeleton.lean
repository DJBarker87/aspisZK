import PV_RJ4IDB_OpenInputs
set_option autoImplicit false
namespace PV_L1E_CountSkeleton
open PV_RJ4IDB
variable {I A : Type}

/-- Acquisition from the source-world call log, before any native decoding.
The two families are independent inputs. This remains a producer obligation. -/
def PV_L1E_Link_CountAcquisition (actualCount : I → List Nat × List Nat)
    (sourceWorld : I → Trace A) : Prop :=
  ∀ i, actualCount i = (counts (sourceWorld i).events,rejections (sourceWorld i).events)

/-- Full ordered body-wrapper trace, including the terminal status, not merely
complete-Result erasure. No native leaf events follow from erasure alone. -/
def PV_L1E_Link_BodyWrapper (sourceWorld bodyWorld : I → Trace A) : Prop :=
  ∀ i, sourceWorld i = bodyWorld i

/-- Full recursive retry/client join onto the ORIGINAL experiment's trace.
The caller supplies its original trace family; this definition does not select
new seeds, failure events, prefixes, or a simulator. -/
def PV_L1E_Link_RetryJoin (bodyWorld originalWorld : I → Trace A) : Prop :=
  ∀ i, bodyWorld i = originalWorld i

/-- Native event/world coupling on the SAME original experiment. This includes
cross-channel order and all terminal forms, and is strictly stronger than the
COUNT input. It is an open V167 association, never a new trust field. -/
def PV_L1E_Link_NativeOriginal (originalWorld : I → Trace A)
    (native : I → NativeTrace A) : Prop :=
  ∀ i, originalWorld i = modelTrace (native i)

/-- Top-down interface check. I is unrestricted: in particular it must include
every admitted interrupted or divergent finite prefix in the concrete instance.
This theorem does not construct that instance or discharge its four links. -/
theorem count_trace (actualCount : I → List Nat × List Nat)
    (native : I → NativeTrace A) (sourceWorld bodyWorld originalWorld : I → Trace A)
    (acquisition : PV_L1E_Link_CountAcquisition actualCount sourceWorld)
    (body : PV_L1E_Link_BodyWrapper sourceWorld bodyWorld)
    (retry : PV_L1E_Link_RetryJoin bodyWorld originalWorld)
    (coupling : PV_L1E_Link_NativeOriginal originalWorld native) :
    PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native := by
  intro i
  rw [acquisition i,body i,retry i,coupling i]
  change (counts ((native i).events.map translateEvent),
    rejections ((native i).events.map translateEvent)) = _
  rw [nativeCounts_translation,nativeRejections_translation]
#print count_trace
#print axioms count_trace
end PV_L1E_CountSkeleton
