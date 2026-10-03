# R434 actual fold closure inventory

This is a mechanical inventory of two frozen inputs. It records source text, LLBC declaration rows, and encoded call/drop/unwind nodes. It makes no alias, lifetime, frame, or Rust-to-LLBC execution claim.

The frozen source is `r429-actual-freeze-fold/materialized-release-check/input/relation_callback.rs`, SHA-256 `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`. The LLBC is `r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc`, SHA-256 `df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358`. Exact selected rows are retained in `R431-exact-rows.json`; `call-drop-unwind-sites.json` retains the selected rows' recursively enumerated `Call` and `Drop` nodes, including nested unwind statements.

## Frozen caller text

The exact numbered excerpt is in `frozen-source-excerpt.txt`.

| Source line | Text/site | Recorded role |
|---|---|---|
| 129 | `record.extend(bytes(&w.v[359..388]))` | First byte slice appended to the record before absorb |
| 131 | `record.extend(bytes(&w.v[388..417]))` | Second byte slice appended to the later record |
| 134 | `let batch=|v:&[K]|{let mut g=K::ONE;v.iter().fold(K::ZERO,|a,v|{let r=a.add(g.mul(*v));g=g.mul(gamma);r})};` | Batch closure source text |
| 136 | `batch(&w.v[359..388])` and `batch(&w.v[388..417])` | Both batch call expressions in slope construction |
| 137 | `batch(&w.v[359..388])` | First batch call in `iv` construction |

## Captured closure places and calls in LLBC

Function IDs and statement IDs below are in the preserved R431 LLBC rows. Local numbers refer to that function's local table; the exact typed place expressions remain in the JSON rows.

| Item | LLBC fact |
|---|---|
| Outer closure call | Fun29 is `aspis_v8_performance_host::freeze::{Trait:4}::call`, source span line 134. It initializes local4 from global13 at statement 8587, then statement 8599 creates a mutable reference from local4 into local8 (type Deduplicated3330). Statement 8602 constructs Type50 from moves of local8 and local9. |
| Shared gamma capture | In Fun29 statement 8601, local9 is assigned a shared `Ref` whose place path is `Local1 → Deref → Field({Adt:26},0) → Deref`; its type is Deduplicated3331. Type50 field 1 has `Ref(Free 1, Deduplicated544, Shared)`. |
| Mutable captured power field | Type50 field 0 has `Ref(Free 0, Deduplicated544, Mut)`. Fun112 statement 11907 reads through the receiver's Type50 field 0 and dereferences it into local8. Statement 11939 assigns a moved local10 back through that same receiver field path. These are the serialized place expressions; no non-aliasing or lifetime conclusion is asserted. |
| Fold setup and invocation | Fun29 statement 8595 calls Fun43 with `Move(Local6)`, destination Local5. Statement 8609 calls Fun70 with arguments `Move(Local5)`, `Copy(Global14)`, `Move(Local7)` and destination Local0. Both call nodes retain their full `on_unwind` rows. |
| `FnOnce::call_once` | Fun111 is closure impl trait 34 method `call_once`. Statement 11887 dispatches trait impl 35 method 0 with arguments `Move(Local3)` and `Move(Local2)`, destination Local0. Statement 11892 drops receiver Local1 with precise drop function Fun144. Both nodes' unwind rows are retained. |
| `FnMut::call_mut` | Fun112 is closure impl trait 35 method `call_mut`. Statement 11915 calls Fun24 with `Move(Local8), Move(Local9)` to Local7; 11923 calls Fun124 with `Move(Local6), Move(Local7)` to Local5; 11936 calls Fun24 with `Move(Local11), Move(Local12)` to Local10. Each call's unwind cleanup is retained. Statement 11939 moves Local10 into the captured field place; statement 11941 copies Local5 into return Local0. |

## Drop and unwind inventory

The complete recursively extracted call/drop nodes are in `call-drop-unwind-sites.json`; this includes nested `on_unwind` lists rather than only top-level statements. At the relevant outer level:

- Fun29's Fun43 call (statement 8595) unwinds through StorageDead locals 3, 2, 1 and UnwindResume. Its Fun70 call (statement 8609) unwinds through StorageDead locals 3, 2, 1 and UnwindResume.
- Fun111's trait dispatch (statement 11887) includes cleanup of local1 by precise Fun144 drop on the call unwind path. The following normal Drop of local1 (statement 11892) has its own unwind path. Both are preserved with their nested cleanup statements.
- Fun112's calls at statements 11915, 11923, and 11936 preserve their respective local cleanup / UnwindResume chains. All additional nested Drop nodes and their unwind actions are included in the machine-generated site file.

`inventory.json` records source/LLBC hashes, exact included declaration IDs, source spans, and the fact boundary. `SHA256SUMS` covers the inventory files and generator. No compilation or source modification was performed for this inventory.
