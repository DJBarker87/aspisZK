# D984 source-store writer inventory v2

Criterion: every source-store cell, including pointers into BoxNew/Arc allocations. This supersedes the v1 exclusion of Arc counts. The OWNER-aware base remains OwnInitInterpreterBridged.

SPEC-C3: `codex/pv-lib-spec-20261107@f2798a4fac4`, `PV_LIB_SPEC_F361ArcMachineGap.native_poll/count_unchanged/increment_impossible`, focused49735: f360 at12950 leaves a source-store strong count unchanged. This is a local mismatch, not original-entry reachability.

## Writer candidates and exact emitted sites

| Function | Footprint | Sites (caller/site) |
|---|---|---|
| thread:f9 alloc::vec::into_iter::impl[12]::next | IntoIter.ptr or end | thread:f1/487, thread:f15/3756, thread:f703/25724 |
| thread:f10 alloc::vec::impl[inherent]::append | destination RawVec/len and source len | thread:f1/930 |
| thread:f93 core::iter::range::impl[4]::next | Range.start | thread:f15/3447 |
| thread:f167 alloc::vec::impl[inherent]::push | Vec.RawVec/len and element destination | thread:f15/3519, thread:f15/3641, thread:f15/4327 |
| thread:f289 core::cell::impl[inherent]::replace | Cell value (transparent scalar on ACTIVE path; boxed layout at other instantiations) | thread:f207/8248 |
| thread:f351 core::sync::atomic::impl[inherent]::fetch_add | AtomicUsize.v.UnsafeCell.value; ArcInner strong and ScopeData running count | thread:f261/9718, thread:f360/11955, thread:f457/17212 |
| thread:f581 core::sync::atomic::impl[inherent]::fetch_sub | AtomicUsize.v.UnsafeCell.value; ArcInner strong/weak and ScopeData running count | thread:f486/21732, thread:f488/21850, thread:f611/23440, thread:f704/25877 |
| thread:f557 core::sync::atomic::impl[inherent]::store | AtomicUsize.v.UnsafeCell.value; weak-count lock or other atomic | thread:f466/20887, thread:f525/22200 |
| thread:f646 core::sync::atomic::impl[inherent]::store | AtomicBool.v.UnsafeCell.value; ScopeData.a_thread_panicked | thread:f611/23421 |
| thread:f442 core::mem::replace | destination pointee | thread:f352/11697 |
| thread:f308 core::ptr::mut_ptr::impl[inherent]::write | destination pointee | thread:f213/8972, thread:f213/9004, thread:f485/21654, thread:f485/21689 |
| thread:f364 core::ptr::write | destination pointee | thread:f272/10416, thread:f288/10769, thread:f473/21237 |
| thread:f504 core::cell::impl[inherent]::set | Cell.value.UnsafeCell.value | thread:f417/16394, thread:f437/16726, thread:f477/21355, thread:f602/23286, thread:f629/24365, thread:f762/26332 |
| thread:f641 core::cell::impl[inherent]::take | Cell.value.UnsafeCell.value := Default::default() | thread:f602/23258 |
| thread:f530 core::sync::atomic::impl[inherent]::compare_exchange_weak | AtomicUsize.v.UnsafeCell.value only on successful CAS; weak spurious failure preserved | thread:f452/16957 |
| thread:f555 core::sync::atomic::impl[inherent]::compare_exchange | AtomicUsize.v.UnsafeCell.value only on successful CAS | thread:f466/20832 |
| thread:f360 alloc::sync::impl[78]::clone | ArcInner.strong.AtomicUsize.v.UnsafeCell.value via Arc.ptr.NonNull.pointer | thread:f270/10098, thread:f361/12950 |
| thread:f683 alloc::sync::impl[188]::drop | ArcInner.weak.AtomicUsize.v.UnsafeCell.value, except dangling Weak | thread:f661/25308 |
| thread:f457 std::thread::scoped::impl[inherent]::increment_num_running_threads | ScopeData.num_running_threads; overflow path decrements again | thread:f361/13713 |
| thread:f611 std::thread::scoped::impl[inherent]::decrement_num_running_threads | ScopeData.num_running_threads and conditional a_thread_panicked | thread:f536/22525 |
| thread:f486 alloc::sync::impl[134]::drop | ArcInner.strong; last-strong branch also drops data and weak guard | thread:f405/16285 |
| thread:f584 alloc::sync::impl[inherent]::drop_slow | ArcInner.data destructor, then implicit weak decrement even on unwind | thread:f486/21818 |

Each JSON entry lists affected ledger rows and whether it is an installed native boundary or a nested emitted candidate. Arc drop486/slow584 and scope decrement611 are emitted bodies; their primitive actions must not also be applied as whole-body summaries when those bodies are expanded. Weak drop683 is opaque. Typed Drop requests require dispatch by their emitted type, not a guessed function ID.

## Atomic reads, Cell and wrappers

Atomic load127/129/528, fence582, Cell get18/600, get_mut368, constructors121/123/371/455 and Cell into_inner763 do not write an existing source cell. Loads remain returned-value obligations. Cell replace289/set504/take641 and pointer writes308/364 are writers even if their receiver points inside a box. No RefCell function is emitted; this is not a purity result for arbitrary callback/destructor types.

The JSON retains all 75 installed LEAF boundaries and all 340 raw thread LEAFs, with every known site and affected rows. 16 installed native wrappers and all type-dependent Drop sites remain REVIEW obligations. They are **not** certified no-write. In particular join168, Thread clone214, spawn hooks454 and scoped increment457 cannot acquire source-effect credit solely from a nested atomic table entry.

## Status and limits

Inventory stage is conservative and incomplete at opaque-wrapper/type-drop effects. The v2 machine work must retain those open obligations. No prior native frame or graph at one of these writers transports unchanged. No new endpoint premise/T field, success restriction or arbitrary Store transformer is permitted. Complete wrapper/type-drop semantics before claiming the full D984 correction or continuing the requested caller histories.
