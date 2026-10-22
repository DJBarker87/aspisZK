#!/usr/bin/env python3
"""Verify the retained WideExact byte decoder source/body binding.

This checker pins source and generated-body identity only. It does not claim
the Aeneas translation theorem or Rust/Lean semantic preservation.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[5]
P = ROOT / "docs/research/100bit-spend-path-20261013"
LINEAGE = P / "evidence/session-b-concrete-finish-field-20261020/original-worker-publication/lineage"
RECORD_INPUT = P / "evidence/record-parser-local-extraction-20261015/parse-record-f-header-array-20261015/source"
CURRENT_RUST = ROOT / "crates/aspis-core/src/field/wide_exact.rs"
RECORD_FUNS = LINEAGE / "lean/RecordParserFuns.lean"
VIEW_FUNS = LINEAGE / "lean/ViewParseCallerFuns.lean"
ECHECK_FUNS = P / "lean/AspisR1EcheckCut/Funs.lean"
CANON_PACKET = P / "evidence/stage2-resume-prefix-canonical-20261020"
CANON_SOURCE = CANON_PACKET / "sources/Stage2ResumeConcreteDecoderCanonicality.lean"
BYTE_CANON_SOURCE = P / "lean/ExtractedRecordByteCanonicality.lean"
LIMB_CANON_SOURCE = P / "evidence/s3-actual-field-parser-readback-v1-20261020/sources/dependencies/ExtractedRecordLimbCanonicality.lean"

EXPECTED = {
    "current_rust_file": "6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b",
    "from_le_bytes_method": "0e5c8f656afd474c7627ce0583343ee9a84d77cc444a326ad1ffb70726a43048",
    "from_limbs_method": "a805372c272d0b1fc1e021817b90b1132e5e020c831a3f143777bcf16f7ed1d2",
    "from_le_bytes_lean_body": "832844fa385d93f30202055a43df94812407c608108bd10643eba63c60ceadfe",
    "from_limbs_lean_body": "09ae848debe1a06817002114a9a2403b3e56394422351377d0f29631d7d635ca",
    "record_parser_funs": "f6a3d5b95b781458af5a0118b76d39a14243b77958ef86eb9e5cac50ac45a2b1",
    "view_parse_funs": "4c6ec91bc31fe62f939d134c13e0a43c5bb445b7e482228bc5591879108c65ff",
    "echeck_funs": "84570e165c409ad20b4cd4c20d2edc6fb92ef92a0bbc34bb54994f38e60b51c3",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rust_method(data: bytes, doc_prefix: str, name: str) -> bytes:
    source = data.decode()
    start = source.index(doc_prefix)
    method = source.index(f"pub fn {name}", start)
    brace = source.index("{", method)
    depth = 0
    for i in range(brace, len(source)):
        if source[i] == "{":
            depth += 1
        elif source[i] == "}":
            depth -= 1
            if depth == 0:
                return source[start : i + 1].encode()
    raise AssertionError(f"unclosed Rust method {name}")


def lean_body(path: Path, name: str) -> bytes:
    source = path.read_text()
    marker = f"def field.wide_exact.WideExact.{name}\n"
    start = source.index(marker) + len(marker)
    end = source.find("\n/--", start)
    if end < 0:
        end = len(source)
    return source[start:end].strip().encode()


def require(label: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(label)


def main() -> None:
    require("RecordParser Funs source pin", sha(RECORD_FUNS.read_bytes()) == EXPECTED["record_parser_funs"])
    require("ViewParse Funs source pin", sha(VIEW_FUNS.read_bytes()) == EXPECTED["view_parse_funs"])
    require("EcheckCut Funs source pin", sha(ECHECK_FUNS.read_bytes()) == EXPECTED["echeck_funs"])
    current = CURRENT_RUST.read_bytes()
    retained_current = (LINEAGE / "rust/current_wide_exact.rs").read_bytes()
    require("current Rust file hash", sha(current) == EXPECTED["current_rust_file"])
    require("retained current Rust file is byte-identical", current == retained_current)

    fragments = {
        "from_le_bytes": RECORD_INPUT / "fragments/wide_from_le_bytes.rs",
        "from_limbs": RECORD_INPUT / "fragments/wide_from_limbs.rs",
    }
    manifest = json.loads((RECORD_INPUT / "source-manifest.json").read_text())
    for name, doc in (
        ("from_le_bytes", "    /// Exactly 32 bytes: eight little-endian u32 limbs"),
        ("from_limbs", "    /// Decode eight base-P digits without reduction"),
    ):
        actual = rust_method(current, doc, name)
        retained = fragments[name].read_bytes()
        expected = EXPECTED[f"{name}_method"]
        require(f"{name} actual method hash", sha(actual) == expected)
        require(f"{name} exact retained source fragment", actual == retained)
        fragment_path = f"fragments/wide_{name}.rs"
        entry = next(item for item in manifest["items"] if item["fragment_path"] == fragment_path)
        require(
            f"{name} source manifest hash",
            sha(retained) == entry["fragment_sha256"] == expected,
        )

    for name in ("from_le_bytes", "from_limbs"):
        bodies = [lean_body(f, name) for f in (RECORD_FUNS, VIEW_FUNS, ECHECK_FUNS)]
        expected = EXPECTED[f"{name}_lean_body"]
        require(f"{name} Lean body expected hash", sha(bodies[0]) == expected)
        require(f"{name} all generated bodies identical", bodies[0] == bodies[1] == bodies[2])

    echeck_manifest = json.loads(
        (P / "evidence/echeck-and-conservation-source-20261016/namespace-adapter/manifest.json").read_text()
    )
    require(
        "EcheckCut generated Funs file pin",
        sha(ECHECK_FUNS.read_bytes()) == echeck_manifest["generated_outputs"]["Funs.lean"]["sha256"],
    )

    canonical_manifest = json.loads((CANON_PACKET / "manifest.json").read_text())
    canonical_entry = next(
        item for item in canonical_manifest["modules"]
        if item["module"] == "Stage2ResumeConcreteDecoderCanonicality"
    )
    require("canonicality source owner hash", sha(CANON_SOURCE.read_bytes()) == canonical_entry["source_sha256"])
    require("canonicality producer object pin", canonical_entry["object_sha256"] == "da5f7f4bee6e4c769516bc7279d86982724b61960447036e1759113c451d32c9")
    canonical_receipt = json.loads((CANON_PACKET / "attempt/receipt.json").read_text())
    require("canonicality receipt target success", canonical_receipt["exit_status"] == 0)
    canonical_source = CANON_SOURCE.read_text()
    require("actualWideDecoder canonicality theorem present", "actualWideDecoder_success_canonical" in canonical_source)
    require("canonicality proof consumes byte slice theorem", "ExtractedRecordByteCanonicality.slice_success" in canonical_source)
    require("byte canonicality source pin", sha(BYTE_CANON_SOURCE.read_bytes()) == "3ad68b76909d82ba93126b0de4ac5eca66df6e628f246e6d2e1688c2c304825d")
    limb_source = LIMB_CANON_SOURCE.read_text()
    require("from_limbs canonical constructor theorem present", "from_limbs_make_success_iff" in limb_source)
    print("PASS: current Rust source, retained parser fragments, and generated method bodies match")
    print("PASS: from_limbs canonicality is consumed by the retained byte-decoder theorem owner")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, KeyError, OSError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
