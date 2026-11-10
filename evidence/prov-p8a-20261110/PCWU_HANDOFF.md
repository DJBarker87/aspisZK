# PCWU_ (P8a) translator lane round 1: handoff (in progress)

Limitation (1) reproduction on frozen roots (4bb3b3f):
- E001 original pair (Charon XRa + Aeneas 959659a6), root fast_pairing::canonical::Dot::push (historic 2731 site XRg ordinal 11), Q::raw opaque: exit 0, no sorry. The 2731 failure does NOT reproduce on the frozen root with the original tool.
- E002 original pair, roots owned::snapshot, stage1, stage2 (stage*_owned opaque): snapshot (try_borrow_data + Ref guard drop) translates; stage1/stage2 fail at Interp.ml:609 "Instantiating the type parameters of a function with types containing mutable borrows" on accounts[i] (SliceIndexShared<AccountInfo<'a>>), not at the guard drop.
- E003 TV3 on the same roots: pending.

Target not yet established
