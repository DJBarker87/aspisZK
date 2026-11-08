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
| thread:f289 core::cell::impl[inherent]::replace | Cell transparent payload, including source-store pointees inside boxes | thread:f207/8248 |
| thread:f351 core::sync::atomic::impl[inherent]::fetch_add | AtomicUsize.v.UnsafeCell.value; ArcInner strong and ScopeData running count | thread:f261/9718, thread:f360/11955, thread:f457/17212 |
| thread:f581 core::sync::atomic::impl[inherent]::fetch_sub | AtomicUsize.v.UnsafeCell.value; ArcInner strong/weak and ScopeData running count | thread:f486/21732, thread:f488/21850, thread:f611/23440, thread:f704/25877 |
| thread:f557 core::sync::atomic::impl[inherent]::store | AtomicUsize.v.UnsafeCell.value; weak-count lock or other atomic | thread:f466/20887, thread:f525/22200 |
| thread:f646 core::sync::atomic::impl[inherent]::store | AtomicBool.v.UnsafeCell.value; ScopeData.a_thread_panicked | thread:f611/23421 |
| thread:f442 core::mem::replace | destination pointee | thread:f352/11697 |
| thread:f308 core::ptr::mut_ptr::impl[inherent]::write | destination pointee | thread:f213/8972, thread:f213/9004, thread:f485/21654, thread:f485/21689 |
| thread:f364 core::ptr::write | destination pointee | thread:f272/10416, thread:f288/10769, thread:f473/21237 |
| thread:f504 core::cell::impl[inherent]::set | transparent Cell payload := new; then Drop(old T), including destructor source writes | thread:f417/16394, thread:f437/16726, thread:f477/21355, thread:f602/23286, thread:f629/24365, thread:f762/26332 |
| thread:f641 core::cell::impl[inherent]::take | transparent Cell payload := SpawnHooks::default() (first=None); old value returned without Drop | thread:f602/23258 |
| thread:f530 core::sync::atomic::impl[inherent]::compare_exchange_weak | AtomicUsize.v.UnsafeCell.value only on successful CAS; weak spurious failure preserved | thread:f452/16957 |
| thread:f555 core::sync::atomic::impl[inherent]::compare_exchange | AtomicUsize.v.UnsafeCell.value only on successful CAS | thread:f466/20832 |
| thread:f360 alloc::sync::impl[78]::clone | ArcInner.strong.AtomicUsize.v.UnsafeCell.value via Arc.ptr.NonNull.pointer | thread:f270/10098, thread:f361/12950 |
| thread:f683 alloc::sync::impl[188]::drop | ArcInner.weak.AtomicUsize.v.UnsafeCell.value, except dangling Weak | thread:f661/25308 |
| thread:f457 std::thread::scoped::impl[inherent]::increment_num_running_threads | ScopeData.num_running_threads; overflow path decrements again | thread:f361/13713 |
| thread:f611 std::thread::scoped::impl[inherent]::decrement_num_running_threads | ScopeData.num_running_threads and conditional a_thread_panicked | thread:f536/22525 |
| thread:f486 alloc::sync::impl[134]::drop | ArcInner.strong; last-strong branch also drops data and weak guard | thread:f405/16285 |
| thread:f584 alloc::sync::impl[inherent]::drop_slow | ArcInner.data destructor, then implicit weak decrement even on unwind | thread:f486/21818 |
| thread:f168 std::thread::scoped::impl[inherent]::join | JoinInner.packet.result.UnsafeCell.value is taken; Arc cleanup also writes counts | thread:f15/3859 |
| thread:f241 core::ptr::copy_nonoverlapping | copy_nonoverlapping destination may be a source-store pointee | thread:f144/5286, thread:f144/5350, thread:f160/7753 |
| thread:f248 core::ptr::drop_in_place | drop_in_place executes the selected destructor | thread:f148/5563, thread:f254/9592, thread:f339/11552, thread:f584/23232 |
| thread:f322 core::ops::drop::Drop::drop | Drop::drop trait dispatch may execute Packet destructor and other captured destructors |  |
| thread:f325 core::ptr::mut_ptr::impl[inherent]::drop_in_place | pointer-method drop_in_place | thread:f229/9342 |
| thread:f454 std::thread::spawnhook::run_spawn_hooks | spawn-hook TLS Cell::take/set and Arc clone/drop; provenance determines source/OWNER backing | thread:f361/12509 |
| thread:f549 core::mem::drop | mem::drop executes the selected destructor | thread:f459/18951, thread:f459/20454, thread:f526/22455, thread:f644/24623, thread:f704/25998 |
| thread:f654 alloc::boxed::impl[175]::drop | Box::drop executes the pointee destructor before deallocation | thread:f618/23804, thread:f618/23841, thread:f618/23888, thread:f618/23925 |
| thread:f4 core::iter::traits::iterator::Iterator::collect | Iterator::collect executes mutable iterator/captured callback, whose source effects need binding | thread:f1/126, thread:f1/1671, thread:f266/9967, thread:f454/17177 |
| thread:f14 aspis_r1_cert_check::native_workers::ordered_map_inner::impl[2]::call | ordered_map_inner closure invokes the user callback; source effects need actual callback binding | thread:f13/3333, thread:f15/3561, thread:f267/9984 |
| thread:f214 std::thread::thread::impl[49]::clone | Thread::clone clones its Arc<Inner>; source count write if Inner is source-backed (OWNER operator path also exists) | thread:f122/4909, thread:f212/8716, thread:f361/14535, thread:f618/23640 |
| thread:f122 std::thread::current::current_or_unnamed | current_or_unnamed clones existing Thread or constructs TLS Thread; backing/provenance unresolved | thread:f6/1820 |
| thread:f128 std::thread::thread::impl[inherent]::park | Thread::park delegates to Parker whose atomic state may be source-backed | thread:f6/2404 |
| thread:f225 std::sys::sync::thread_parking::futex::impl[inherent]::park | Parker::park changes the atomic parker state through Pin<&Parker> | thread:f128/5052 |
| thread:f669 std::sys::sync::thread_parking::futex::impl[inherent]::unpark | Parker::unpark swaps atomic state before a possible futex wake | thread:f647/24676 |
| thread:f309 std::sys::sync::thread_parking::futex::impl[inherent]::new_in_place | Parker::new_in_place writes through its destination pointer | thread:f213/9034 |
| thread:f296 std::sys::thread_local::native::impl[inherent]::set | thread-local Storage::set replaces the stored payload through the receiver | thread:f212/8591, thread:f212/8821, thread:f651/24907 |
| thread:f369 core::option::impl[inherent]::take | Option::take replaces the referenced Option by None without dropping its old payload | thread:f274/10518, thread:f644/24548 |
| thread:f538 libc::unix::pthread_attr_init | pthread_attr_init writes pointed-to pthread_attr_t storage | thread:f459/17448 |
| thread:f544 libc::unix::pthread_attr_setstacksize | pthread_attr_setstacksize writes pointed-to pthread_attr_t storage | thread:f459/18262, thread:f459/19536 |
| thread:f548 libc::new::common::posix::pthread::pthread_create | pthread_create writes thread ID through its output pointer and invokes callback | thread:f459/18727, thread:f459/20230 |
| thread:f648 libc::unix::pthread_attr_destroy | pthread_attr_destroy may invalidate the pointed-to attributes | thread:f613/23506 |
| thread:f510 alloc::raw_vec::impl[inherent]::deallocate | RawVec::deallocate invalidates backing allocation; source-cell lifetime mapping unresolved | thread:f422/16502 |
| thread:f622 alloc::raw_vec::impl[inherent]::finish_grow | RawVec::finish_grow may allocate/reallocate source-backed storage; resource channel unresolved | thread:f552/22879 |
| thread:f19 core::iter::traits::iterator::Iterator::next_chunk | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f23 core::iter::traits::iterator::Iterator::advance_by | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f52 core::iter::traits::iterator::Iterator::try_fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f54 core::iter::traits::iterator::Iterator::fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f92 core::iter::traits::iterator::Iterator::__iterator_get_unchecked | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f97 core::iter::range::impl[4]::advance_by | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f102 core::iter::range::impl[4]::__iterator_get_unchecked | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f114 core::iter::adapters::map::impl[6]::next | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f116 core::iter::adapters::map::impl[6]::try_fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f117 core::iter::adapters::map::impl[6]::fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f118 core::iter::adapters::map::impl[6]::__iterator_get_unchecked | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f120 core::iter::adapters::map::Map::impl[8]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f157 core::option::Option::impl[14]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f158 alloc::boxed::Box::impl[15]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f163 core::result::Result::impl[16]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f176 core::iter::traits::double_ended::DoubleEndedIterator::advance_back_by | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f228 alloc::alloc::Global::impl[30]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f250 core::option::impl[inherent]::map_or | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f148/5594, thread:f339/11583 |
| thread:f295 core::option::impl[inherent]::unwrap_or_else | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f211/8308, thread:f361/12111 |
| thread:f300 std::io::Write::write_fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open | thread:f212/8503, thread:f262/9855, thread:f618/24131 |
| thread:f311 core::pin::impl[77]::clone | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f214/9114 |
| thread:f318 core::intrinsics::catch_unwind | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f219/9196 |
| thread:f343 aspis_r1_cert_check::<slice>::impl[59]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f362 std::io::error::impl[63]::fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f409 core::pin::Pin::impl[80]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f412 core::fmt::impl[82]::fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f415 core::hash::impls::impl[84]::hash | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f425 core::iter::traits::iterator::impl[87]::next | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f427 core::iter::traits::iterator::impl[87]::advance_by | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f429 core::iter::traits::iterator::impl[87]::try_fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f430 core::iter::traits::iterator::impl[87]::fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f444 core::fmt::num::imp::impl[93]::fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f470 core::fmt::impl[inherent]::debug_struct | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open | thread:f376/15941 |
| thread:f471 core::fmt::builders::impl[inherent]::finish | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open | thread:f376/15948 |
| thread:f481 alloc::ffi::c_str::impl[106]::fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f482 alloc::sync::impl[inherent]::new_uninit_in::impl[107]::call_once | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f484 core::result::impl[inherent]::unwrap_or_else | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f403/16223 |
| thread:f516 core::fmt::impl[inherent]::write_str | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open | thread:f441/16787 |
| thread:f553 std::io::error::impl[120]::fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f554 std::io::error::Error::impl[121]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f570 core::option::impl[130]::clone | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f642/24498 |
| thread:f589 aspis_r1_cert_check::<tuple_2>::impl[137]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f597 core::option::impl[inherent]::and_then | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f525/22169, thread:f634/24418, thread:f644/24576 |
| thread:f609 core::iter::sources::successors::impl[145]::next | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f615 core::mem::drop_guard::DropGuard::impl[148]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f620 alloc::boxed::impl[162]::call_once | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim | thread:f547/22662, thread:f703/25782 |
| thread:f627 core::alloc::layout::impl[151]::fmt | Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open |  |
| thread:f645 core::mem::maybe_dangling::MaybeDangling::impl[161]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f655 std::sys::pal::unix::stack_overflow::Handler::impl[163]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f657 alloc::collections::TryReserveErrorKind::impl[165]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f685 std::ffi::os_str::OsString::impl[179]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |
| thread:f698 core::iter::adapters::zip::impl[198]::next | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding | thread:f678/25470 |
| thread:f717 core::slice::iter::impl[196]::next | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f718 core::slice::iter::impl[196]::next_chunk | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f722 core::slice::iter::impl[196]::advance_by | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f725 core::slice::iter::impl[196]::fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f733 core::slice::iter::impl[196]::__iterator_get_unchecked | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f737 core::iter::adapters::zip::impl[198]::fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f738 core::iter::adapters::zip::impl[198]::__iterator_get_unchecked | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f739 core::slice::iter::impl[199]::next | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f740 core::slice::iter::impl[199]::next_chunk | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f744 core::slice::iter::impl[199]::advance_by | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f747 core::slice::iter::impl[199]::fold | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f754 core::slice::iter::impl[199]::__iterator_get_unchecked | Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding |  |
| thread:f756 core::num::error::ParseIntError::impl[201]::drop_glue | Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim |  |

Each JSON entry lists affected ledger rows and whether it is an installed native boundary or a nested emitted candidate. Arc drop486/slow584 and scope decrement611 are emitted bodies; their primitive actions must not also be applied as whole-body summaries when those bodies are expanded. Weak drop683 is opaque. Typed Drop requests require dispatch by their emitted type, not a guessed function ID.

## Atomic reads, Cell and wrappers

Atomic load127/129/528, fence582, Cell get18/600, UnsafeCell::get_mut368, Atomic constructors121/123, Cell::new371, UnsafeCell::new455 and Cell::into_inner763 do not write an existing source cell. Loads remain returned-value obligations. Cell replace289/set504/take641 and pointer writes308/364 are writers even if their receiver points inside a box. No RefCell function is emitted; this is not a purity result for arbitrary callback/destructor types.

The JSON retains all 75 installed LEAF boundaries and all 340 raw thread LEAFs, with every known site and affected rows. 8 installed native wrappers and all type-dependent Drop sites remain REVIEW obligations. They are **not** certified no-write. In particular join168, Thread clone214, spawn hooks454 and scoped increment457 cannot acquire source-effect credit solely from a nested atomic table entry.

## Status and limits

Inventory stage is conservative and incomplete at opaque-wrapper/type-drop effects. The v2 machine work must retain those open obligations. No prior native frame or graph at one of these writers transports unchanged. No new endpoint premise/T field, success restriction or arbitrary Store transformer is permitted. Complete wrapper/type-drop semantics before claiming the full D984 correction or continuing the requested caller histories.

## Compiled projection coverage (session5)

The final partial candidate is `PV_LIB_A_DropDispatchV2.step`, extending the
OWNER-aware base through `OwnerStoreV3`. Original five plus17 new function
projections are compiled. `session5/STORE_ACTIONS.json` gives named meanings,
exact source hashes, attempts, sites, affected rows and open coverage for every
inventory candidate. Atomic loads127/129/528 have named returned-value facts;
they do not write source cells. Full backend/order/backing bindings are open.

Arc486/Weak683 are supported ONLY on source-selected nonlast counts; last,
dangling, deallocation and typed payload Drop are not supplied. Cell504 is
supported ONLY for bool; generic old-value Drop is open. Transparent641 and
numeric-byte646 supersede the wrong wrapped/boolean-data drafts, which receive
no source credit despite passing mathematical axiom audits. No missing full
meaning is replaced by a guessed Store transformer. The inventory's111 entries
are conservative writer/callback candidates, not111 proved actual writers.
Eight further installed wrappers remain REVIEW, as explicitly listed in JSON.

Strict raw47490 passed118 roots from28 new modules (standard axioms only),
including superseded mathematical definitions for reproducibility. The audit
proves no source/model adequacy. No slot status, row consumer, endpoint premise,
T field, ledger or frozen specification was changed. D984 and complete caller
histories remain unfinished; unused focused IDs are not budget exhaustion.
