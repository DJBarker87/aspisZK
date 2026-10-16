#!/usr/bin/env python3
"""Limited source-review aid; not a Rust parser or a refinement theorem.

Compare token bodies in four R1 modules and the three shared Merkle bodies.
Normalizations are digest-call spelling, generic Merkle names and, when
present, expansion of the separately reviewed exact public_transcript helper.
Signatures, implementations, concrete call sites and runtime effects require
separate review. No source, compiler, build artifact or wallet is modified.
"""
import argparse
import json
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("baseline")
parser.add_argument("candidate")
args = parser.parse_args()
token = re.compile(
    r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|'
    r"'(?:\\.|[^'\\])'|[A-Za-z_][A-Za-z_0-9]*|[0-9][A-Za-z_0-9]*|[^\s]"
)


def source(revision, path):
    return subprocess.check_output(["git", "show", revision + ":" + path], text=True)


def functions(text):
    ts = [m.group() for m in token.finditer(text)
          if not m.group().startswith(("//", "/*"))]
    found = {}
    i = 0
    while i < len(ts) - 1:
        if ts[i] != "fn" or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", ts[i + 1]):
            i += 1
            continue
        name = ts[i + 1]
        j = i + 2
        # These selected files contain definitions, not abstract declarations.
        # Semicolons inside array parameter types are not declaration endings.
        while ts[j] != "{":
            j += 1
        depth, k = 1, j + 1
        while depth:
            depth += (ts[k] == "{") - (ts[k] == "}")
            k += 1
        found.setdefault(name, []).append(ts[j:k])
        i = k
    return found


def normalized(tokens):
    text = " ".join(tokens)
    text = text.replace("self . hash . digest (", "( self . hash ) (")
    text = text.replace("hash . digest (", "hash (")
    for name in ("leaf", "parent", "private_leaf_hash"):
        text = text.replace(name + "_with_digest", name)
    return text


checked = []
factorings = []
for module in ("r1_wire", "r1_semantic", "transcript", "verifier"):
    path = "crates/aspis-r1-cost-probe/src/" + module + ".rs"
    before = functions(source(args.baseline, path).split("#[cfg(test)]")[0])
    after = functions(source(args.candidate, path).split("#[cfg(test)]")[0])
    if module == "r1_semantic" and "public_transcript" in after:
        expected = functions("""fn expected() {
            SemanticTranscript::new(hash,
                &public.public_bytes().map_err(|_| Error::Public)?, c1_root,)
        }""")["expected"]
        assert after.pop("public_transcript") == expected, "public_transcript body"
        short = "public_transcript ( public , hash , prefix . c1_root )"
        expanded = ("SemanticTranscript : : new ( hash , & public . public_bytes ( ) "
                    ". map_err ( | _ | Error : : Public ) ? , prefix . c1_root , )")
        for index, body in enumerate(after["verify_observed"]):
            joined = " ".join(body)
            assert joined.count(short) == 1, "public_transcript call count"
            after["verify_observed"][index] = joined.replace(short, expanded).split(" ")
        checked.append([path, "public_transcript exact body", 0])
        factorings.append("public_transcript exact body/call expansion")
    assert before.keys() == after.keys(), path
    for name in before:
        assert len(before[name]) == len(after[name]), (path, name)
        for index, (old, new) in enumerate(zip(before[name], after[name])):
            assert normalized(old) == normalized(new), (path, name, index)
            checked.append([path, name, index])
for path, names in (
    ("crates/aspis-core/src/r0/merkle.rs", ("leaf", "parent")),
    ("crates/aspis-core/src/state_only_private_merkle.rs", ("private_leaf_hash",)),
):
    before, after = functions(source(args.baseline, path)), functions(source(args.candidate, path))
    for name in names:
        assert normalized(before[name][0]) == normalized(after[name + "_with_digest"][0]), (path, name)
        checked.append([path, name + " => " + name + "_with_digest", 0])
print(json.dumps({
    "baseline": args.baseline, "candidate": args.candidate,
    "status": "PASS", "checked_function_bodies": len(checked), "functions": checked,
    "reviewed_factorings": factorings,
    "scope": "Limited token-body source comparison only; separate signature, backend, wrapper, instantiation and runtime review required.",
}, indent=2))
