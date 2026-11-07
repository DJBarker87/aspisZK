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
