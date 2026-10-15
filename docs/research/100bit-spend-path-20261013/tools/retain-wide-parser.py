#!/usr/bin/env python3
"""Check exact new Wide parser declarations and reuse of old QM31 declarations.

Only the enclosing generated namespace is relocated. Shared declarations must
be byte-identical to the previously checked generated declarations (including
source comments). This is a source-retention check, not compiler correctness.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import tarfile

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "docs/research/100bit-spend-path-20261013"
EVIDENCE = BASE / "evidence/wide-parser-extraction-20261015"
PREVIOUS = BASE / "evidence/field-parser-candidate-retention-20261014/input/AspisR1CandidateParser"
OUTPUT = BASE / "lean/CandidateWideParserSource.lean"
PINS = {
    "generated/AspisR1WideParser/Types.lean": "bcaea7bdaf254ff94e734f23c99c63f5c6f84c5314343411dd011155180e45c6",
    "generated/AspisR1WideParser/Funs.lean": "64fcce682d289cd6570ca1b081c8706eac68acb9cf9abd35280058bf89080157",
    "generated/translation.json": "0c4dece0fca191ea19d2f8a4043e5699d93b4ab2f41946783c9cf00122e636ae",
    "attempt-d.tar.gz": "9060ac5e168eb15b8d2127894e40a19cd84ea616e8f27a4224de2a0850641b45",
    "input-b/field.rs": "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea",
    "input-b/field/wide_exact.rs": "940e31f8056b6a3b9422d3fa31ae6cbe3c4084d79885bb8fd5b4a14c56dd7d06"
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blocks(text, namespace):
    start = "namespace " + namespace + "\n"
    end = "\nend " + namespace
    assert text.count(start) == text.count(end) == 1
    body = text.split(start, 1)[1].split(end, 1)[0].strip()
    chunks = re.split(r"(?=/-- \[)", body)
    result = {}
    for chunk in chunks:
        if not chunk.strip():
            continue
        match = re.search(r"(?:^|\n)(?:@\[[^\n]*\] )?(?:def|structure)\s+([A-Za-z0-9_.]+)", chunk)
        assert match, chunk[:150]
        name = match.group(1)
        assert name not in result, name
        result[name] = chunk.strip()
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    for name, expected in PINS.items():
        assert sha((EVIDENCE/name).read_bytes()) == expected, name
    types = blocks((EVIDENCE/"generated/AspisR1WideParser/Types.lean").read_text(), "AspisR1WideParser")
    funs = blocks((EVIDENCE/"generated/AspisR1WideParser/Funs.lean").read_text(), "AspisR1WideParser")
    old_types = blocks((PREVIOUS/"Types.lean").read_text(), "AspisR1CandidateParser")
    old_funs = blocks((PREVIOUS/"Funs.lean").read_text(), "AspisR1CandidateParser")
    assert set(types) == set(old_types) | {"field.wide_exact.WideExact"}
    for name in old_types:
        assert types[name] == old_types[name], name
    shared = set(old_funs) - {"parse_fields_probe"}
    for name in shared:
        assert funs[name] == old_funs[name], name
    added = ["field.wide_exact.WideExact.BYTE_LEN", "field.wide_exact.WideExact.from_le_bytes", "parse_wide_exact_probe"]
    assert set(funs) == shared | set(added)
    meta = json.loads((EVIDENCE/"generated/translation.json").read_text())
    assert len(meta["functions"]) == 7 and all(not x["is_opaque"] for x in meta["functions"])
    with tarfile.open(EVIDENCE/"attempt-d.tar.gz") as archive:
        members = archive.getmembers()
        def read_suffix(suffix):
            matching = [m for m in members if m.name.endswith(suffix)]
            assert len(matching) == 1, suffix
            return archive.extractfile(matching[0]).read()
        for source in ["field.rs", "field/wide_exact.rs"]:
            assert read_suffix("/source/"+source) == (EVIDENCE/"input-b"/source).read_bytes()
        for source in ["Types.lean", "Funs.lean"]:
            assert read_suffix("/generated/AspisR1WideParser/"+source) == (EVIDENCE/"generated/AspisR1WideParser"/source).read_bytes()
        llbc = json.loads(read_suffix("/R1FieldParser.llbc"))["translated"]
        options = [x for x in llbc["type_decls"] if isinstance(x,dict) and x.get("item_meta",{}).get("lang_item")=="Option"]
        assert len(options)==1
        option = options[0]
        file_id = option["item_meta"]["span"]["data"]["file_id"]
        assert next(x for x in llbc["files"] if x["id"]==file_id)["name"] == {"Local":"/rustc/library/core/src/option.rs"}
        assert [(x["name"],x["discriminant"]) for x in option["kind"]["Enum"]] == [
            ("None",{"Scalar":{"Signed":["Isize","0"]}}),
            ("Some",{"Scalar":{"Signed":["Isize","1"]}})]
    header = """import R1CandidateFieldParsers

/-! Exact newly generated Wide parser declarations, relocated into the already
checked candidate parser namespace. All shared field and Option declarations
are byte-identical and reused by import; tools/retain-wide-parser.py checks
this partition against the full generated Types/Funs and LLBC metadata.
This isolated candidate is not yet the deployed/runtime Wide parser. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1CandidateParser

"""
    body = "\n\n".join([types["field.wide_exact.WideExact"]]+[funs[x] for x in added])
    audits = "\n".join("#print axioms AspisR1CandidateParser."+x for x in ["field.wide_exact.WideExact",*added])
    expected = header + body + "\n\nend AspisR1CandidateParser\n\n" + audits + "\n"
    if args.write:
        OUTPUT.write_text(expected)
    assert OUTPUT.read_text() == expected
    assert not re.search(r"(?m)^\s*(axiom|opaque|sorryAx)\b", expected)
    print(json.dumps({"shared_types":len(old_types),"shared_functions_and_globals":len(shared),"new_declarations":4,"nonopaque_functions":7,"retained_sha256":sha(OUTPUT.read_bytes()),"all_checks_passed":True},indent=2))

if __name__ == "__main__":
    main()
