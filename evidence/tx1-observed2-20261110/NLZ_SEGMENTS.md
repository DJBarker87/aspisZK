# NLZ segments

All native segments initially OPEN. Retired NLJ K023/K028/K029 and NLR K001 are not replayed.

| Cut | Source line | Segment contract | Control | Verdict |
|---|---|---|---|---|
|137 entry→parse|312|original bytes, exact parse arguments, readonly resources|pending|OPEN|
|137 parse→mark0|312–313|complete Prefix root/27 original windows, Err/abort cleanup|pending|OPEN|
|137 mark0→public|313–314|same Public/hash/root, full frame|pending|OPEN|
|137 public→begin|314–315|exact transcript, Prefix, hash ownership|pending|OPEN|
|137 begin→mark1|315–316|arbitrary complete challenge reply and transcript writeback, Err prefix|pending|OPEN|
|137 mark1→finish|316–317|same Public/Prefix/transcript/challenges, full RowSpec136|pending|OPEN|
|137 finish→return|317|full Verified/Box identity or every Err/abort and external frame|pending|OPEN|
|087 entry→filled|256|allocator request14759, Allocation mapping, scratch frame|pending|OPEN|
|087 filled→expandSemantic|256–258|owned logical split13831/928, compressed source slice|pending|OPEN|
|087 expandSemantic→expandValues|258–259|same expanded semantic owner and source y1 slice|pending|OPEN|
|087 expandValues→wideView|259–260|all windows, mutable writebacks, lifetimes|pending|OPEN|
|087 wideView→137|260–261|same Public/hash/semantic and full RowSpec137|pending|OPEN|
|087137→mark|261–262|exact Semantic mapping, complete Verified owner|pending|OPEN|
|087 mark→179|262–263|same semantic/view/hash/scratch; full179 caller domain|pending|OPEN|
|087179→return|263|Prepared owner/scratch writeback and all error/abort cleanup|pending|OPEN|

## Retained candidate evidence; no full contract verdict

| Actual cut | Native candidates | Control kind | Current verdict |
|---|---|---|---|
|parse Err→return|K004 /K002|inverted assertion|local support; argument/full-frame contract OPEN|
|parse/mark0→public|K005 /K006 plus argument assertions in later windows|inverted assertion; initial pair Transfer-only|full(y) corruption control and physical state OPEN|
|public→begin|K017/018 metadata;K019/020 transcript state|inverted assertions|split support; full modifies/resource interpretation OPEN|
|begin/mark1→finish|K009/010 metadata;K021/022 state;K023/024 full Challenges|inverted assertions|split support; full136 packet/domain OPEN|
|all returning Err prefixes and full input byte frame|K011–016|inverted assertions|candidate no-suffix/value/frame support; full contract OPEN|
|finish→Ok Verified return|K027/028 roots byte;K029/030 challenges/alpha;K031/032 claims owner/cell;K033/034 extra;K035/036 before_z1;K037/038 state;K039/040 z/transcript|corrupted logged child reply, same configuration|seven positive/control pairs; physical owner/heap/ghost-erasure composition OPEN|
|087 allocation/split/expansion/view/137/179/return|none|none|native OPEN; source/window support only|

K007/K008 andK025 timed out90s and are retired; K026 hit the assertion library's memcmp64 unwind bound, replaced with arbitrary root-byte selection. No timeout, unwind or memory cap was increased. All passes remain SUPPORT, not complete(ay)(3) contracts: complete explicit parent heap/allocator/ownership state and exact modifies sets have not been proved. The current Chain's Occurrence records are not a resource semantics.
