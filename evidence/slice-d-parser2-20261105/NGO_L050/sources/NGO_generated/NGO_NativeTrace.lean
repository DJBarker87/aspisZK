import NGO_ScheduleState
import NGO_FirstError
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_NativeTrace
open NGD_DecodeTrace AspisR1DecodeKFullV10
abbrev Native := NGO_ScheduleState.Iter
/-- Original chunks/enumerate schedule, recording the SAME typed write or
first-error terminal. Every low input is tied to the original record. -/
inductive Run {N : Usize} {r : Record} {off start : Usize}
    (d : Domain N r off start) : Native → Array Q N → Final N → Prop where
  | done (iter : Native) (out : Array Q N)
      (next : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorChunksExact U8) iter=ok (none,iter)) :
      Run d iter out (out,none)
  | reject (iter nextIter : Native) (out : Array Q N) (index : Usize) (chunk : Slice U8)
      (live : index.val<N.val)
      (next : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorChunksExact U8) iter=ok (some (index,chunk),nextIter))
      (input : chunk.val.take 16=(NGD_DecodeValueLaw.input r off N index
        d.minlen d.cap d.positive live d.range).val)
      (error : r1_wire.Error) (reply : answer d index live=.Err error) :
      Run d iter out (out,some (.Err error))
  | write (iter nextIter : Native) (out updated : Array Q N) (index : Usize) (chunk : Slice U8)
      (live : index.val<N.val)
      (next : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorChunksExact U8) iter=ok (some (index,chunk),nextIter))
      (input : chunk.val.take 16=(NGD_DecodeValueLaw.input r off N index
        d.minlen d.cap d.positive live d.range).val)
      (q : Q) (reply : answer d index live=.Ok q)
      (store : Array.update out index q=ok updated) (final : Final N)
      (rest : Run d nextIter updated final) : Run d iter out final
end NGO_NativeTrace
