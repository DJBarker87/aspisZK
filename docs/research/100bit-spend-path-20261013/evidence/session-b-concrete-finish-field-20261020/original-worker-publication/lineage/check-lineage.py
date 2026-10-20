#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent.parent
def read(rel): return (root/rel).read_bytes()
def rust_method(b):
 s=b.decode(); start=s.index("    /// Exactly 32 bytes: eight little-endian u32 limbs"); i=s.index("    pub fn from_le_bytes",start); brace=s.index("{",i); depth=0
 for j in range(brace,len(s)):
  if s[j]=="{": depth+=1
  elif s[j]=="}":
   depth-=1
   if depth==0:return s[start:j+1].encode()
 raise ValueError("unclosed method")
def lean_body(b):
 s=b.decode(); i=s.index("def field.wide_exact.WideExact.from_le_bytes\n")+len("def field.wide_exact.WideExact.from_le_bytes\n"); j=s.find("\n/--",i); return s[i:j if j>=0 else len(s)].strip().encode()
rust=[rust_method(read(p)) for p in ["lineage/rust/current_wide_exact.rs","lineage/rust/frozen_c8_wide_exact.rs","lineage/rust/record_parser_wide_from_le_bytes.rs"]]
lean=[lean_body(read(p)) for p in ["lineage/lean/RecordParserFuns.lean","lineage/lean/ViewParseCallerFuns.lean"]]
assert rust[0]==rust[1]==rust[2]
assert lean[0]==lean[1]
report={"rust_method_sha256":hashlib.sha256(rust[0]).hexdigest(),"rust_method_bytes":len(rust[0]),"rust_sources_equal":True,"generated_lean_body_sha256":hashlib.sha256(lean[0]).hexdigest(),"generated_lean_body_bytes":len(lean[0]),"record_parser_equals_view_parse_body":True,"scope":"Literal source/body equality only; does not prove Aeneas translation correctness."}
print(json.dumps(report,indent=2))
(root/"lineage/check-report.json").write_text(json.dumps(report,indent=2)+"\n")
