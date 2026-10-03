#!/usr/bin/env python3
"""Read-only inventory of the exact R427 attempt-C framed MIR text."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FRAME = ROOT / "mir-frame.txt"
OUT = ROOT / "inventory.json"
raw = FRAME.read_bytes()
text = raw.decode("utf-8")
lines = text.splitlines(keepends=True)

# Byte offsets are computed from original UTF-8 bytes; this frame is ASCII, but
# keep the computation correct if a future debug string contains UTF-8.
offsets=[]
cur=0
for line in lines:
    offsets.append(cur)
    cur += len(line.encode("utf-8"))

def rec_line(i, kind=None):
    s=lines[i].rstrip("\r\n")
    return {"line_1based": i+1, "byte_start": offsets[i], "byte_end": offsets[i]+len(lines[i].encode("utf-8")), "kind":kind, "raw":s}

begin=[i for i,l in enumerate(lines) if l.startswith("ASPIS_R427_RAW_MIR_BEGIN ")]
end=[i for i,l in enumerate(lines) if l.startswith("ASPIS_R427_RAW_MIR_END ")]
if len(begin)!=1 or len(end)!=1 or begin[0]>=end[0]:
    raise SystemExit(f"expected one ordered frame: begin={begin}, end={end}")
bm=re.fullmatch(r"ASPIS_R427_RAW_MIR_BEGIN name=(\S+) def_id=(.*)\n?",lines[begin[0]].rstrip("\r\n"))
em=re.fullmatch(r"ASPIS_R427_RAW_MIR_END name=(\S+) def_id=(.*)\n?",lines[end[0]].rstrip("\r\n"))
if not bm or not em or bm.groups()!=em.groups():
    raise SystemExit("begin/end name or DefId mismatch")

prefixes={
 "display_name":"ASPIS_R427_DISPLAY_NAME ",
 "statement_source":"ASPIS_R427_STATEMENT_SOURCE ",
 "use_retag":"ASPIS_R427_USE_RETAG ",
 "terminator_source":"ASPIS_R427_TERMINATOR_SOURCE ",
 "call_arg":"ASPIS_R427_CALL_ARG ",
}
markers=[]
for i,line in enumerate(lines):
    for kind,prefix in prefixes.items():
        if line.startswith(prefix):
            r=rec_line(i,kind)
            m=re.search(r"\bbb=(bb\d+)\b",line)
            if m:r["bb"]=m.group(1)
            mi=re.search(r"\bindex=(\d+)\b",line)
            if mi:r["index"]=int(mi.group(1))
            if kind=="call_arg":
                m2=re.search(r"\boperand=(.*?) span=(.*)$",line.rstrip("\r\n"))
                r["operand"]=m2.group(1) if m2 else None
                r["span"]=m2.group(2) if m2 else None
            markers.append(r)
            break

# `BasicBlockData` entries are printed in index order inside the one body.
# Exact indentation identifies outer vector entries; preserve each raw block.
block_starts=[i for i,l in enumerate(lines) if l == "            BasicBlockData {\n"]
blocks=[]
for n,st in enumerate(block_starts):
    en=None
    for j in range(st+1,len(lines)):
        if lines[j] == "            },\n":
            en=j
            break
    if en is None: raise SystemExit(f"no end for BasicBlockData at line {st+1}")
    # Avoid accidentally spanning into next block if formatting changes.
    if n+1<len(block_starts) and en>block_starts[n+1]:
        raise SystemExit(f"overlapping basic blocks at line {st+1}")
    term_starts=[j for j in range(st,en+1) if lines[j].strip()=="terminator: Some("]
    term=None
    if term_starts:
        ts=term_starts[0]
        te=next((j for j in range(ts+1,en+1) if lines[j]=="                ),\n"),None)
        if te is None: raise SystemExit(f"no terminator close at block line {st+1}")
        term={"line_start_1based":ts+1,"line_end_1based":te+1,
              "byte_start":offsets[ts],"byte_end":offsets[te]+len(lines[te].encode()),
              "raw":"".join(lines[ts:te+1]).rstrip("\r\n")}
    blocks.append({"bb":f"bb{n}","line_start_1based":st+1,"line_end_1based":en+1,
                   "byte_start":offsets[st],"byte_end":offsets[en]+len(lines[en].encode()),
                   "terminator":term})

call_args={}
for m in markers:
    if m["kind"]=="call_arg": call_args.setdefault(m["bb"],[]).append(m)
call_blocks=[]
for b in blocks:
    args=call_args.get(b["bb"],[])
    if args:
        call_blocks.append({"bb":b["bb"],"block_line_span":[b["line_start_1based"],b["line_end_1based"]],
                            "block_byte_span":[b["byte_start"],b["byte_end"]],
                            "terminator":b["terminator"],"call_arg_markers":args})

# all source records, retags, terminator records are retained verbatim above;
# summarize counts and the specific next-call entry by exact MIR text selector.
next_calls=[]
for c in call_blocks:
    term=c["terminator"] or {}
    if "::next(" in term.get("raw",""):
        next_calls.append(c)

out={
 "classification":"read-only native Rustc MIR text inventory; no ownership or source-correspondence claim",
 "frame":{"target_name":bm.group(1),"def_id_debug":bm.group(2),"begin_line":begin[0]+1,"end_line":end[0]+1,
          "byte_start":offsets[begin[0]],"byte_end":offsets[end[0]]+len(lines[end[0]].encode()),
          "sha256":hashlib.sha256(raw).hexdigest(),"byte_count":len(raw),"line_count":len(lines),
          "complete_copy":"mir-frame.txt"},
 "counts":{"basic_blocks":len(blocks),"markers":len(markers),
           "statement_source":sum(m['kind']=='statement_source' for m in markers),
           "use_retag":sum(m['kind']=='use_retag' for m in markers),
           "terminator_source":sum(m['kind']=='terminator_source' for m in markers),
           "call_arg":sum(m['kind']=='call_arg' for m in markers),
           "call_blocks_with_argument_markers":len(call_blocks)},
 "display_name_markers":[m for m in markers if m['kind']=='display_name'],
 "blocks":blocks,
 "call_blocks":call_blocks,
 "next_call_candidates":next_calls,
 "all_markers":markers,
 "limitations":["The inventory copies printed fields literally; it does not infer source ownership, borrow, or MIR-to-Rust semantics.",
                "The call set is the set of blocks having emitted CALL_ARG markers, cross-referenced to their printed full terminator."]
}
OUT.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"frame_sha256":out['frame']['sha256'],"counts":out['counts'],"next_candidates":[{"bb":c['bb'],"terminator":c['terminator']['raw'],"args":[(a['index'],a['operand'],a['span']) for a in c['call_arg_markers']]} for c in next_calls]},indent=2))
