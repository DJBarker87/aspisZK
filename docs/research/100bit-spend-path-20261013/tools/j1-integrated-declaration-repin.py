#!/usr/bin/env python3
"""Read/hash-only accepted/current extraction inventory at an explicit Git ref.

No compiler, Lean, runtime, RPC or SBF invocation. Supplements are explicit,
content-pinned inputs for not-yet-committed worker evidence; merged-tip replay
normally needs none. Missing/ambiguous source correspondence is never dropped.
"""
from pathlib import Path
import argparse
import collections
import difflib
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[4]
BASE = "docs/research/100bit-spend-path-20261013"
SEED = BASE + "/design/J1-DIGEST32-EXTRACTED-DECLARATION-REPIN-20261016.json"
KINDS = {"type_decls": "types", "fun_decls": "functions", "global_decls": "globals",
         "trait_decls": "trait_decls", "trait_impls": "trait_impls"}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
canonical = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
RUST_CACHE = {}


def uncomment(text):
    out = []; i = 0; depth = 0
    while i < len(text):
        if text[i:i+2] == "/-": depth += 1; i += 2
        elif depth and text[i:i+2] == "-/": depth -= 1; i += 2
        elif depth: i += 1
        elif text[i:i+2] == "--":
            end = text.find("\n", i); i = len(text) if end < 0 else end
        elif text[i] == '"':
            start = i; i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            out.append(text[start:i])
        else: out.append(text[i]); i += 1
    return "".join(out)


def lean_tokens(text):
    return re.findall(r'"(?:\\.|[^"\\])*"|[^\s"]+', uncomment(text))


def lean_declarations(raw):
    """Same token convention as C's 79-declaration audit; also cover impl_def."""
    text = uncomment(raw.decode())
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:def|structure|inductive|abbrev|instance|impl_def|trait_def|opaque)\s+(\S+)", re.M)
    matches = list(pat.finditer(text)); result = {}
    for i, match in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else text.rfind("\nend ")
        if end < match.end(): end = len(text)
        body = re.sub(r"\s*@\[[^\]]*\]\s*$", "", text[match.start():end])
        name = match[1]; tok = lean_tokens(body)
        if name in result:
            name += "@anonymous:" + str(text.count("\n", 0, match.start()) + 1)
        split = tok.index(":=") if ":=" in tok else len(tok)
        # Types' complete constructor/field statements belong to the signature.
        if any(word in tok[:4] for word in ["structure", "inductive"]): split = len(tok)
        result[name] = {"tokens": tok, "body_sha256": sha(canonical(tok)),
                        "signature": " ".join(tok[:split]),
                        "signature_sha256": sha(canonical(tok[:split]))}
    return result


class Inputs:
    def __init__(self, revision, supplements):
        self.revision = revision; self.supplements = supplements; self.pins = {}

    def git(self, revision, path):
        return subprocess.check_output(["git", "-C", str(ROOT), "show", revision + ":" + path], stderr=subprocess.DEVNULL)

    def read(self, path, optional=False):
        try:
            raw = self.git(self.revision, path); origin = "git:" + self.revision
        except subprocess.CalledProcessError:
            found = next((p / path for p in self.supplements if (p / path).is_file()), None)
            if found is None:
                if optional: return None
                raise ValueError("Required inventory input missing at ref/supplements: " + path)
            raw = found.read_bytes(); origin = "explicit-supplement"
        self.pins[path] = {"sha256": sha(raw), "origin": origin}
        return raw

    def json(self, path, optional=False):
        raw = self.read(path, optional)
        return json.loads(raw) if raw is not None else None


def positions(raw):
    out = [0]
    for line in raw.splitlines(keepends=True): out.append(out[-1] + len(line))
    return out


def span_bytes(raw, span):
    offsets = positions(raw)
    start = offsets[span["beg"]["line"] - 1] + span["beg"]["col"]
    end = offsets[span["end"]["line"] - 1] + span["end"]["col"]
    return raw[start:end], start, end


def rust_context(raw, start, end, audit):
    """Lexical impl/generic and owner-type context, separately from body bytes.

    Namespace-only kit module wrappers are intentionally excluded. This is a
    source-context identity check, not a Rust type-resolution/refinement proof.
    """
    fragment = raw[start:end].decode()
    # Rust/LLBC provenance offsets are byte offsets; the lexer uses Python
    # character indices. Preserve that distinction for Unicode comments.
    start = len(raw[:start].decode()); end = len(raw[:end].decode())
    key = sha(raw)
    if key not in RUST_CACHE:
        text = raw.decode(); ts = audit.tokens(text); pairs = audit.brackets(ts)
        RUST_CACHE[key] = (text, ts, pairs)
    text, ts, pairs = RUST_CACHE[key]
    impls = []; functions = []
    for i, token in enumerate(ts):
        if token[0] != "{" or not token[1] <= start < ts[pairs[i]][2]: continue
        j = i - 1
        while j >= 0:
            if ts[j][0] in [")", "]"]: j = pairs[j] - 1
            elif ts[j][0] in [";", "{", "}"]: break
            else: j -= 1
        header = [t[0] for t in ts[j+1:i]]
        if "impl" in header and not any(k in header[:header.index("impl")] for k in ["fn", "struct", "enum"]):
            impls.append(header)
        if "fn" in header:
            first = ts[j+1][1]; last = ts[pairs[i]][2]
            functions.append({"header_tokens": header,
                "complete_enclosing_function_sha256": sha(text[first:last].encode()),
                "relative_character_start": start-first,
                "relative_character_end": end-first})
    owners = []
    identifiers = {t for h in impls for t in h}
    # Derive source spans can be only #[derive(...)], so bind the following type.
    attribute_start = text.rfind("#[derive", 0, start+1)
    derive = fragment.lstrip().startswith("#[derive") or (
        attribute_start >= 0 and text.find("]", attribute_start) >= end)
    for i, token in enumerate(ts):
        if token[0] not in ["struct", "enum", "type"] or i+1 >= len(ts): continue
        name = ts[i+1][0]
        if name not in identifiers and not (derive and token[1] >= end and token[1] - end < 512): continue
        j = i + 1
        while j < len(ts) and ts[j][0] not in ["{", ";"]:
            if ts[j][0] in ["(", "["]: j = pairs[j] + 1
            else: j += 1
        if j == len(ts): continue
        stop = pairs[j] + 1 if ts[j][0] == "{" else j + 1
        owners.append({"name": name, "tokens": [t[0] for t in ts[i:stop]]})
        if derive: break
    value = {"enclosing_impl_headers": impls, "enclosing_functions": functions, "owner_types": owners}
    return {"sha256": sha(canonical(value)), "details": value}


class Cone:
    def __init__(self, name, files, llbc_name, kit, inputs, archive_pin=None):
        self.name = name; self.files = files; self.llbc_name = llbc_name
        self.raw = files[llbc_name]; self.data = json.loads(self.raw)["translated"]
        self.kit = kit or {}; self.inputs = inputs; self.archive_pin = archive_pin
        translations = [n for n in files if n.endswith("translation.json")]
        self.translation = json.loads(files[translations[0]]) if translations else {}
        self.generated = {}
        for file, raw in files.items():
            if file.endswith(".lean"):
                for name, item in lean_declarations(raw).items():
                    self.generated.setdefault(name, item)

    def item(self, kind, ident):
        return next((x for x in self.data[kind] if x and x.get("def_id") == ident), None)

    def source(self, item):
        meta = item["item_meta"]; span = meta["span"]["data"]
        file = self.data["files"][span["file_id"]]
        path = file["name"].get("Local", file["name"].get("Virtual", ""))
        contents = file.get("contents")
        raw = contents.encode() if contents is not None else None
        text = meta.get("source_text")
        if raw is not None:
            extracted, start, end = span_bytes(raw, span)
            if text is None: text = extracted.decode()
        else:
            rev = self.kit.get("source_revision", self.kit.get("revision"))
            if rev and not path.startswith(("/rustc/", "/cargo/")):
                try: raw = self.inputs.git(rev, path)
                except subprocess.CalledProcessError: pass
            if raw is not None:
                extracted, start, end = span_bytes(raw, span)
                if text is None: text = extracted.decode()
            else: start = end = None
        if raw is not None and text is not None and raw[start:end] != text.encode():
            matches = [m.start() for m in re.finditer(re.escape(text.encode()), raw)]
            if matches:
                # Source text is authoritative; columns can use a different
                # Unicode convention. Bind to the nearest retained exact span.
                start = min(matches, key=lambda at: abs(at-start)); end = start+len(text.encode())
        return path, raw, text.encode() if text is not None else None, start, end

    def signatures(self, kind, ident):
        matches = [q for q in self.translation.get(KINDS[kind], []) if q.get("def_id") == ident]
        output = []
        for q in matches:
            name = q["lean_name"]; short = name.split(".", 1)[-1]
            generated = self.generated.get(short, self.generated.get(name))
            output.append({"lean_name": name, "lean_file": q.get("lean_file"), "is_opaque": q.get("is_opaque", False),
                           **({k: generated[k] for k in ["body_sha256", "signature", "signature_sha256"]} if generated else {})})
        item = self.item(kind, ident)
        llbc_sig = {key: item[key] for key in ["generics", "signature", "kind", "type", "impl_trait"] if key in item}
        return {"generated": output, "llbc_signature_sha256": sha(canonical(llbc_sig)), "llbc_signature": llbc_sig}


def archive_cone(spec, inputs):
    path = spec["archive"]; raw = inputs.read(path)
    with tarfile.open(fileobj=io.BytesIO(raw)) as tar:
        # Keep only source metadata/generated text, not compiled objects/caches.
        files = {m.name: tar.extractfile(m).read() for m in tar.getmembers()
                 if m.isfile() and (m.name == spec["llbc_member"] or m.name.endswith(("translation.json", ".lean")))}
    if spec.get("accepted_prefix"):
        prefix = spec["accepted_prefix"]
        files = {name: body for name, body in files.items() if name.startswith(prefix) or name == spec["llbc_member"]}
        assert spec["llbc_member"] in files
        assert sum(name.endswith("translation.json") for name in files) == 1, "Accepted prefix must select exactly one backend translation"
    kit = inputs.json(BASE + "/tools/" + spec["kit"]) if spec.get("kit") else None
    return Cone(spec["cone"], files, spec["llbc_member"], kit, inputs,
                {"path": path, "sha256": sha(raw), "llbc_member": spec["llbc_member"], "llbc_sha256": sha(files[spec["llbc_member"]]), "accepted_prefix": spec.get("accepted_prefix")})



def verified_fragment_layout(cone, spec, inputs):
    """Verify exact historical cuts and their occurrence in the LLBC's kit lib.

    Membership comes from source pins, not a current-source text lookup. Stubs
    outside these cuts are never accepted as production declaration bodies.
    """
    kit = cone.kit
    directory = BASE + "/tools/" + spec["kit"].rsplit("/", 1)[0] + "/"
    artifacts = {name: inputs.read(directory + name) for name in kit["kit_files"]}
    for name, raw in artifacts.items(): assert sha(raw) == kit["kit_files"][name], (cone.name, name)
    lib = artifacts["lib.rs"]
    retained = [f["contents"].encode() for f in cone.data["files"]
        if f["name"].get("Local") == "lib.rs" and f.get("contents") is not None]
    assert retained == [lib], "Accepted LLBC must contain exact registered kit lib.rs"
    base = json.loads(artifacts["base52/source-pins.json"])
    assert sha(artifacts["base52/lib.rs"]) == kit["base52_lib_sha256"] == base["kit_files"]["lib.rs"]
    assert kit["base52_cuts"] == base["cuts"]
    layout = []; missing = []
    for category, cuts, revision in [("base52", kit["base52_cuts"], base["revision"]),
                                     ("fragment", kit["cuts"], kit["revision"])]:
        for cut in cuts:
            source = inputs.git(revision, cut["path"])
            body = source[cut["start_byte"]:cut["end_byte_exclusive"]]
            assert sha(body) == cut["sha256"], (cone.name, category, cut["name"], "historical source pin")
            if category == "fragment": assert artifacts["fragments/" + cut["name"] + ".rs"] == body
            matches = [m.start() for m in re.finditer(re.escape(body), lib)]
            if not matches:
                missing.append({"category": category, "name": cut["name"], "path": cut["path"],
                    "sha256": cut["sha256"], "reason": "Inherited cut not present in final kit; not used for source membership"})
            for at in matches:
                layout.append({"category": category, "name": cut["name"], "path": cut["path"],
                    "start_byte": at, "end_byte_exclusive": at + len(body),
                    "source_revision": revision, "source_sha256": sha(source),
                    "source_start_byte": cut["start_byte"], "source_end_byte_exclusive": cut["end_byte_exclusive"],
                    "fragment_sha256": sha(body)})
    return lib, layout, {"cone": cone.name, "kit_lib_sha256": sha(lib), "layout": layout,
        "inherited_or_fragment_cuts_not_present": missing,
        "verified_kit_file_count": len(artifacts),
        "basis": "All kit files and historical source cut hashes verified; exact cut occurrences reconstruct layout before current-source lookup"}


def lean_chunks(raw, include_impl_def=False):
    text = uncomment(raw.decode())
    kinds = "def|structure|inductive|abbrev|instance" + ("|impl_def" if include_impl_def else "")
    matches = list(re.finditer(r"^\s*(?:@\[[^\]]*\]\s*)*(?:" + kinds + r")\s+(\S+)", text, re.M))
    return {m[1]: re.sub(r"\s*@\[[^\]]*\]\s*$", "", text[m.start():matches[i+1].start() if i+1 < len(matches) else text.rfind("\nend ")]).strip() + "\n"
        for i, m in enumerate(matches)}


def bound_statement_audits(inputs, specs, cones):
    result = []; assets = {}
    for cone in cones:
        for name, raw in cone.files.items():
            if name.endswith(".lean"): assets[sha(raw)] = (name, raw)
    for spec in specs:
        for path in spec.get("bound_models", []):
            raw = inputs.read(path); assets[sha(raw)] = (path, raw)
        for audit in spec.get("binding_audits", []):
            parent = audit.rsplit("/", 1)[0]
            for name in ["AspisR1PublicPreparation/Types.lean", "AspisR1PublicPreparation/Funs.lean"]:
                raw = inputs.read(parent + "/" + name, optional=True)
                if raw is not None: assets[sha(raw)] = (parent + "/" + name, raw)
    for spec in specs:
        for path in spec.get("binding_audits", []):
            raw = inputs.read(path); record = json.loads(raw); checks = []
            parser = record.get("chunk_parser")
            assert parser in {None, "include_impl_def"}, (path, parser)
            chunks_for_record = lambda data: lean_chunks(data, include_impl_def=parser == "include_impl_def")
            model_items = record.get("model_body_audits", record.get("exact_body_audits", []))
            if model_items:
                funs_hash = record.get("raw_funs_sha256") or record["carrier_inventory"]["Funs.lean"]["raw_current_sha256"]
                assert funs_hash in assets, (path, "raw accepted Funs missing")
                raw_funs = assets[funs_hash][1]; chunks = chunks_for_record(raw_funs)
                mapping = record["identifier_map"]
                pattern = re.compile("|".join(re.escape(n) + r"(?![A-Za-z0-9_.])" for n in sorted(mapping, key=len, reverse=True)))
                for item in model_items:
                    name = item.get("source_declaration", item.get("declaration")); original = chunks[name]
                    assert sha(canonical(lean_tokens(original))) == item["source_token_sha256"], (path, name, "body token pin")
                    body = pattern.sub(lambda m: mapping[m[0]], original); target = mapping[name]
                    binder = item.get("binder_addition", " (B : PreparedModel.Boundaries)" if "sole_binder_addition" in item else "")
                    if binder:
                        head = "def " + target + "\n"; assert head in body
                        body = body.replace(head, "def " + target.split(" ")[0] + binder + "\n", 1)
                    assert sha(body.encode()) == item.get("adapted_sha256", item.get("model_sha256")), (path, name, "exact parameter-bound body")
                    assert any(body.encode() in value[1] for value in assets.values()), (path, name, "bound source absent")
                    before_statement = original.split(":=", 1)[0].strip(); after_statement = body.split(":=", 1)[0].strip()
                    checks.append({"declaration": name, "exact_substitution_and_binder_replayed": True,
                        "source_token_sha256": item["source_token_sha256"], "bound_body_sha256": sha(body.encode()),
                        "generated_statement": before_statement, "parameter_bound_statement": after_statement,
                        "statement_diff": statement_diff(before_statement, after_statement),
                        "complete_declaration_diff": statement_diff(original.rstrip(), body.rstrip())})
                if "model_sha256" in record: assert record["model_sha256"] in assets
                for name, digest in record.get("output_hashes", {}).items(): assert digest in assets, (path, name, "output pin")
            if "canonical_common_types" in record:
                # The complete finish binder uses the current shared carrier
                # files explicitly selected by its cone manifest.
                canonical_types = [p for p in spec.get("bound_models", []) if p.endswith("/Types.lean")]
                canonical_funs = [p for p in spec.get("bound_models", []) if p.endswith("/Funs.lean")]
                assert len(canonical_types) == len(canonical_funs) == 1
                raw_types = chunks_for_record(assets[record["raw_types_sha256"]][1])
                shared_types = chunks_for_record(inputs.read(canonical_types[0]))
                shared_funs = chunks_for_record(inputs.read(canonical_funs[0]))
                raw_funs = chunks_for_record(assets[record["raw_funs_sha256"]][1])
                for item in record["canonical_common_types"]:
                    name = item["declaration"]; before_body = raw_types[name]; body = before_body
                    assert sha(before_body.encode()) == item["raw_sha256"]
                    for rule in item["normalizations"]:
                        if rule == "remove redundant argument parentheses":
                            assert name == "aspis_core.Digest32"
                            body = body.replace("Self → (Slice (Slice Std.U8))", "Self → Slice (Slice Std.U8)")
                        elif rule == "reuse existing canonical named discriminant reader/instance; remove raw deriving attribute only":
                            assert body.startswith("@[discriminant isize]\n") and name + ".read_discriminant" in shared_types
                            body = body.removeprefix("@[discriminant isize]\n")
                        else:
                            raise ValueError("Unknown complete finish carrier normalization: " + rule)
                    assert sha(canonical(lean_tokens(body))) == item["canonical_token_sha256"]
                    assert lean_tokens(body) == lean_tokens(shared_types[name])
                    checks.append({"declaration": name, "canonical_finish_carrier_replayed": True,
                        "statement_diff": statement_diff(before_body, body), "rules": item["normalizations"]})
                for item in record["canonical_function_token_identity"]:
                    name = item["declaration"]
                    assert sha(canonical(lean_tokens(raw_funs[name]))) == item["raw_and_canonical_token_sha256"]
                    assert lean_tokens(raw_funs[name]) == lean_tokens(shared_funs[name])
                    checks.append({"declaration": name, "canonical_function_identity_replayed": True})
                prior_rounds = chunks_for_record(assets[record["accepted_rounds_raw_funs_sha256"]][1])
                assert record["fixed_actual_round_model_source_sha256"] in assets
                for item in record["fixed_round_body_token_identity"]:
                    name = item["declaration"]
                    assert sha(canonical(lean_tokens(raw_funs[name]))) == item["finish_and_accepted_rounds_token_sha256"]
                    assert lean_tokens(raw_funs[name]) == lean_tokens(prior_rounds[name])
                    checks.append({"declaration": name, "fixed_actual_round_body_identity_replayed": True})
            for file, inventory in record.get("carrier_inventory", {}).items():
                digest = inventory["raw_current_sha256"]; assert digest in assets
                chunks = chunks_for_record(assets[digest][1]); normal = inventory.get("explicit_statement_parenthesization_normalizations", {})
                for name, change in normal.items():
                    assert chunks[name] == change["raw_statement"]
                    chunks[name] = change["canonical_statement"]
                    checks.append({"declaration": name, "explicit_normalization_replayed": True,
                        "statement_diff": statement_diff(change["raw_statement"], change["canonical_statement"]), "rule": change["rule"]})
                # The compact round binder records the same canonical overlay
                # as explicit diffs rather than duplicate full declarations.
                # Replay only these five named, syntax-only transformations.
                for name, change in inventory.get("explicit_statement_normalizations", {}).items():
                    before_body = chunks[name]; body = before_body
                    if name == "aspis_core.Digest32":
                        old = "Self → (Slice (Slice Std.U8))"
                        assert body.count(old) == 1
                        body = body.replace(old, "Self → Slice (Slice Std.U8)")
                    elif name == "r1_wire.Error":
                        assert body.startswith("@[discriminant isize]\n")
                        body = body.removeprefix("@[discriminant isize]\n")
                    elif name in {"sampler.qm31_digits_loop0.body", "sampler.qm31_div_pass_loop.body",
                                  "sampler.qm31_digits_loop1.body"}:
                        local = "digits1" if name == "sampler.qm31_digits_loop1.body" else "rank1"
                        pattern = re.compile(r"\b" + local + r"\b")
                        assert len(pattern.findall(body)) == 2
                        body = pattern.sub("a", body)
                    else:
                        raise ValueError("Unrecognized compact carrier normalization: " + name)
                    diff = "".join(difflib.unified_diff(before_body.splitlines(True), body.splitlines(True),
                        fromfile="raw-current", tofile="accepted-canonical"))
                    assert diff == change["statement_diff"], (path, name, "explicit normalization diff")
                    common = record["common_carrier_audit"][file]
                    assert common["prior_source_sha256"] in assets
                    prior_chunks = chunks_for_record(assets[common["prior_source_sha256"]][1])
                    assert lean_tokens(body) == lean_tokens(prior_chunks[name])
                    if name == "r1_wire.Error":
                        assert "r1_wire.Error.read_discriminant" in prior_chunks
                    chunks[name] = body
                    checks.append({"declaration": name, "explicit_normalization_replayed": True,
                        "statement_diff": diff, "rule": change["rule"],
                        "accepted_prior_source_sha256": common["prior_source_sha256"]})
                for item in inventory["common_unchanged"]:
                    digest = sha(canonical(lean_tokens(chunks[item["declaration"]])))
                    assert digest == item["old_token_sha256"] == item["current_token_sha256"], (path, file, item["declaration"])
                checks.append({"file": file, "common_canonical_token_hashes_checked": len(inventory["common_unchanged"])})
            if "common_type_audit" in record:
                assert record["raw_types_sha256"] in assets and record["base_types_sha256"] in assets and record["shared_types_sha256"] in assets
                raw_types = chunks_for_record(assets[record["raw_types_sha256"]][1]); base_types = chunks_for_record(assets[record["base_types_sha256"]][1]); shared_types = chunks_for_record(assets[record["shared_types_sha256"]][1])
                for entry in record["common_type_audit"]:
                    name = entry["declaration"]; before = raw_types[name]; body = before
                    assert sha(before.encode()) == entry["raw_sha256"]
                    for rule in entry["normalizations"]:
                        if rule == "remove redundant argument parentheses": body = body.replace("Self → (Slice (Slice Std.U8))", "Self → Slice (Slice Std.U8)")
                        elif rule == "reuse existing canonical named discriminant reader/instance; remove raw deriving attribute only":
                            assert name + ".read_discriminant" in base_types
                            body = body.removeprefix("@[discriminant isize]\n")
                        else: raise ValueError("Unknown normalization: " + rule)
                    digest = sha(canonical(lean_tokens(body)))
                    assert digest == entry["canonical_token_sha256"] == sha(canonical(lean_tokens(base_types[name]))) == sha(canonical(lean_tokens(shared_types[name])))
                    checks.append({"declaration": name, "common_type_normalizations_replayed": entry["normalizations"], "statement_diff": statement_diff(before, body)})
                for name in record["new_types"]: assert lean_tokens(raw_types[name]) == lean_tokens(shared_types[name])
                assert record["shared_funs_sha256"] in assets
            if "common_funs" in record:
                assert sha(inputs.read(BASE + "/lean/bridge-prepared-3335-20261016/binding-pins.json")) == record["A_prepared_binding_pins_sha256"]
                raw_funs = chunks_for_record(next(c for c in cones if c.name == spec["cone"]).files[next(n for n in next(c for c in cones if c.name == spec["cone"]).files if n.endswith("/Funs.lean"))])
                for entry in record["common_funs"]:
                    name = entry["declaration"]; before = raw_funs[name]; body = before
                    for rule in entry["normalizations"]:
                        match = re.fullmatch(r"Alpha rename local (rank1|digits1)→a \(bind result and its sole return use\)", rule)
                        assert match, (path, rule)
                        pattern = re.compile(r"\b" + match[1] + r"\b"); assert len(pattern.findall(body)) == 2
                        body = pattern.sub("a", body)
                    assert sha(canonical(lean_tokens(body))) == entry["canonical_token_sha256"], (path, name)
                    checks.append({"declaration": name, "common_function_normalizations_replayed": entry["normalizations"], "statement_diff": statement_diff(before, body)})
                for entry in record["same_prepared_model_source_bodies"]:
                    assert entry["same_as_A_prepared_binder"] and sha(canonical(lean_tokens(raw_funs[entry["declaration"]]))) == entry["source_token_sha256"]
            result.append({"cone": spec["cone"], "path": path, "sha256": sha(raw), "record": record, "read_hash_replay": checks,
                "scope": "Exact identifier substitutions, explicit binder additions and listed carrier normalizations replayed from accepted raw emission. Function parameters remain conditional boundaries; external-template stubs/diagnostics are not actual source-body theorems."})
        for path in spec.get("bound_models", []):
            raw = inputs.read(path)
            assert not re.search(rb"^\s*(axiom|opaque)\b", raw, re.M), path
            result.append({"cone": spec["cone"], "model_path": path, "sha256": sha(raw),
                "declarations": {n: {k: v[k] for k in ["body_sha256", "signature", "signature_sha256"]}
                    for n, v in lean_declarations(raw).items()},
                "scope": "Checked-model source hashes; producing proof receipts retained separately, no Lean replay here."})
    return result


def reconcile_followup_statements(rows, cones, followup_names):
    prior = {}; declarations = {}
    for cone in cones:
        for name, item in cone.generated.items(): declarations.setdefault(name, []).append(item)
    for row in [r for r in rows if r["cone"] not in followup_names] + [r for r in rows if r["cone"] in followup_names]:
        outputs = row.get("retained_signature", {}).get("generated", [])
        comparisons = []
        for emitted in outputs:
            name = emitted["lean_name"]; old = prior.get(name)
            if row["cone"] in followup_names and old is not None:
                comparisons.append({"lean_name": name, "previous_body_sha256": old.get("body_sha256"),
                    "current_body_sha256": emitted.get("body_sha256"),
                    "previous_signature_sha256": old.get("signature_sha256"), "current_signature_sha256": emitted.get("signature_sha256"),
                    "statement_diff": statement_diff(old.get("signature", ""), emitted.get("signature", "")),
                    "statement_status": "identical" if old.get("signature_sha256") == emitted.get("signature_sha256") else "changed",
                    "body_status": "identical" if old.get("body_sha256") == emitted.get("body_sha256") else "changed"})
            prior[name] = emitted
        if row["cone"] in followup_names and comparisons:
            row["prior_current_emission_comparison"] = comparisons
            row.pop("previous_statement_status", None)
            row["statement_diff"] = "\n".join(c["statement_diff"] for c in comparisons)
            # Identical generated Lean does not repair missing correspondence
            # to the selected Rust revision. Preserve that unresolved status;
            # otherwise a stale body can be silently promoted to unchanged.
            if row["classification"] != "unresolved" and len(comparisons) == len(outputs) and all(c["statement_status"] == c["body_status"] == "identical" for c in comparisons):
                row["classification"] = "unchanged"
                row["identity_basis"] += " Current and prior retained generated signatures/body token hashes are also identical."
            elif row["classification"] == "unresolved":
                row["generated_diff_status"] = "Generated comparison recorded only; unresolved Rust source correspondence is not repaired by retained Lean identity."
            else:
                row["generated_diff_status"] = "Re-extracted; explicit raw signature diffs shown. Unchanged statement with changed body is recorded separately; canonical naming/alpha/parenthesis normalizations are in the binding audit."

def statement_diff(before, after):
    return "".join(difflib.unified_diff((before + "\n").splitlines(True) if before else [],
        (after + "\n").splitlines(True), fromfile="previous statement" if before else "previous: absent", tofile="current statement"))


def history_index(inputs, selected, changed):
    paths = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only",
        inputs.revision, BASE + "/evidence"], text=True).splitlines()
    archives = []; members = []
    selected_hashes = {sha(q.raw): q.name for q in selected}
    for path in paths:
        if not re.fullmatch(re.escape(BASE) + r"/evidence/[^/]+/[^/]+\.tar\.gz", path): continue
        if "/v7" in path or "/v8" in path: continue
        raw = inputs.read(path); archives.append({"path": path, "sha256": sha(raw), "bytes": len(raw)})
        with tarfile.open(fileobj=io.BytesIO(raw)) as tf:
            for member in tf.getmembers():
                if not member.isfile() or not member.name.endswith(".llbc"): continue
                body = tf.extractfile(member).read(); parsed = json.loads(body)
                data = parsed.get("translated", {}); digest = sha(body)
                files = [f["name"] for f in data.get("files", [])]
                local = [f.get("Local", f.get("Virtual", "")) for f in files]
                aliases = [f for f in local if f == "lib.rs" or f.startswith("programs/adapter-reconstruct/")]
                direct = [f for f in local if any(f == q or f.endswith("/" + q) for q in changed)]
                label = selected_hashes.get(digest)
                replacement = "readonly-account-extraction-20261016" in path
                status = "selected-current-or-accepted" if label else (
                    "authorized-superseded-wrapper" if replacement else "historical-not-selected")
                if not label and "opening-queries-blocker-20261016" in path:
                    status = "rejected-diagnostic-query-emission-not-current"
                elif not label and "tx1-finish-diagnostic/" in member.name:
                    status = "rejected-diagnostic-tx1-tail-emission-not-current"
                elif not label and not replacement and parsed.get("has_errors"):
                    status = "failed-LLBC-not-current"
                elif not label and not replacement and not aliases and not direct:
                    status = "historical-unrelated-source-files"
                members.append({"archive": path, "member": member.name, "sha256": digest,
                    "has_errors": parsed.get("has_errors"), "selected_cone": label,
                    "status": status, "source_file_names": files, "kit_alias_files": aliases,
                    "migration_changed_direct_files": direct,
                    "path_labels": [word for word in ["attempt", "diagnostic", "candidate", "original", "renamed"] if word in path or word in member.name],
                    "counts": {k: sum(x is not None for x in data.get(k, [])) for k in KINDS},
                    "note": "A successful LLBC bit alone is not accepted backend/kernel evidence. Nonselected/failed/obsolete variants remain historical; lib.rs denotes a kit alias, not a production file."})
    return {"archives": archives, "llbc_members": members,
            "archive_count": len(archives), "llbc_member_count": len(members),
            "scope": "Direct LLBC members of the tracked R1 evidence tar.gz universe at the requested ref; nested archive recursion not performed. The earlier218/48 scan is retained separately."}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--revision", required=True)
    ap.add_argument("--migration-before", default="ca137f5db")
    ap.add_argument("--supplement-root", type=Path, action="append", default=[])
    ap.add_argument("--additional-cone", action="append", default=[],
                    help="Repository JSON manifest (or explicit supplement) with cone/archive/llbc_member/optional kit; accepted/current only")
    ap.add_argument("--output", type=Path, default=ROOT / BASE / "design/J1-INTEGRATED-DECLARATION-REPIN-20261016.json")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--require-complete", action="store_true",
                    help="Exit2 if any registered accepted/current declaration is unresolved")
    args = ap.parse_args()
    ref = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", args.revision], text=True).strip()
    before = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", args.migration_before], text=True).strip()
    inputs = Inputs(ref, args.supplement_root)
    audit_path = ROOT / BASE / "tools/j1e-source-effect-audit.py"
    assert audit_path.read_bytes() == inputs.read(BASE + "/tools/j1e-source-effect-audit.py"), "Lexer must match requested Git ref"
    spec = importlib.util.spec_from_file_location("rust_lexical_audit", audit_path)
    audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
    seed = inputs.json(SEED)
    changed = subprocess.check_output(["git", "-C", str(ROOT), "diff", "--name-only", before, ref, "--", "*.rs"], text=True).splitlines()
    changed = sorted(p for p in changed if p.startswith(("crates/", "programs/")))
    current = {p: inputs.git(ref, p) for p in changed if subprocess.run(["git", "-C", str(ROOT), "cat-file", "-e", ref + ":" + p], stderr=subprocess.DEVNULL).returncode == 0}
    cones = {q["cone"]: archive_cone(q, inputs) for q in seed["inputs"]}
    rows = []; unresolved = []; synthetic = []

    def correspond(row, historical, source_raw, start, end, signature, fresh=False):
        target = row["source_path"]; now = current.get(target)
        # Retained accepted membership can predate the selected migration
        # baseline. Such files still need source correspondence; absence from
        # git diff does not mean absence from the current tree.
        if now is None:
            try:
                now = inputs.git(ref, target); current[target] = now
            except subprocess.CalledProcessError:
                pass
        result = dict(row, retained_signature=signature,
            source_file_changed_since_migration_before=target in changed)
        # An opaque API never supplied an implementation theorem. Re-pin its
        # exact Rust header and owner context, retaining both body hashes as
        # unproved provenance; do not require or claim unchanged body bytes.
        if (row.get("emission_kind") == "opaque-boundary-signature-only"
                and historical is not None and b"fn " in historical):
            original_boundary = historical
            opening = next((t[1] for t in audit.tokens(historical.decode()) if t[0] == "{"), None)
            if opening is not None:
                historical = historical[:opening].rstrip()
                end = start + len(historical) if start is not None else end
                result.update(source_identity_scope="Opaque Rust signature only; no implementation was emitted or proved",
                    historical_unproved_declaration_sha256=sha(original_boundary),
                    opaque_rust_header_sha256=sha(historical))
        if now is None or historical is None or source_raw is None or start is None:
            result.update(classification="unresolved", reason="Missing current source, historical declaration bytes, or enclosing-source provenance")
        else:
            pattern = re.escape(historical)
            if re.fullmatch(rb"[A-Za-z_][A-Za-z_0-9]*", historical):
                pattern = rb"(?<![A-Za-z_0-9])" + pattern + rb"(?![A-Za-z_0-9])"
            matches = [m.start() for m in re.finditer(pattern, now)]
            old_context = rust_context(source_raw, start, end, audit) if source_raw is not None and start is not None else None
            candidates = [(at, rust_context(now, at, at + len(historical), audit)) for at in matches]
            if old_context is not None: candidates = [q for q in candidates if q[1]["sha256"] == old_context["sha256"]]
            if len(candidates) != 1:
                result.update(classification="unresolved", reason="Declaration absent/ambiguous or enclosing impl/owner context changed", exact_body_occurrences=len(matches), context_matching_occurrences=len(candidates), historical_context=old_context)
            else:
                at, context = candidates[0]
                result.update(classification="re-extracted" if fresh else "unchanged",
                    source_body_sha256=sha(historical), enclosing_context=context,
                    historical_enclosing_context_sha256=old_context["sha256"],
                    current_start_byte=at, current_end_byte_exclusive=at+len(historical), current_file_sha256=sha(now),
                    identity_basis="Exact source body plus enclosing impl/owner-type tokens; retained generated/LLBC signature separately hashed. This is not a Rust name-resolution/refinement proof.")
                if result.get("source_identity_scope"):
                    result["identity_basis"] = "Exact unchanged opaque Rust header and enclosing owner context, plus retained LLBC/API signature. No unchanged implementation or source-body theorem is claimed."
                    try:
                        actual_declaration = audit.fragment(now, historical.decode())[0].encode()
                        result["current_unproved_declaration_sha256"] = sha(actual_declaration)
                        result["unproved_source_body_changed"] = sha(actual_declaration) != result["historical_unproved_declaration_sha256"]
                    except ValueError:
                        result["current_unproved_declaration_sha256"] = None
                if fresh:
                    text = "\n".join(q.get("signature", q["lean_name"]) for q in signature.get("generated", [])) or json.dumps(signature.get("llbc_signature", {}), sort_keys=True)
                    result["statement_diff"] = statement_diff("", text)
                    result["previous_statement_status"] = "No prior accepted emission for this current declaration in the enumerated cones"
        if result["classification"] == "unresolved": unresolved.append({"name": result.get("name"), "source_path": target, "reason": result["reason"]})
        rows.append(result)

    # Historical accepted LLBC universe: the seed is a membership index, not an
    # authority for the new classification. Re-read each actual LLBC/body/context.
    for old in seed["declarations"]:
        cone_name = old["cone"]
        if cone_name == "readonly-account-superseded":
            wrapper = inputs.json(BASE + "/tools/readonly-meta-extraction-kit/source-pins.json")["sources"][0]["declarations"]["require_readonly_account"]["declaration"].encode()
            raw = current[old["source_path"]]; at = raw.find(wrapper)
            if at < 0 or raw.find(wrapper, at+1) >= 0: raise ValueError("Current authorized wrapper is absent/ambiguous")
            rows.append({**old, "classification": "authorized-helper-projection-replacement",
                "actual_AccountInfo_wrapper_emitted": False,
                "replacement": "Actual emitted readonly_meta_ok; one still-conditional R16ReadonlyMetadataProjection shared with readonly_buffer_meta_ok. Custody remains separate.",
                "source_revision": ref, "source_body_sha256": sha(wrapper),
                "current_file_sha256": sha(raw), "current_start_byte": at, "current_end_byte_exclusive": at+len(wrapper),
                "enclosing_context": rust_context(raw, at, at+len(wrapper), audit)})
            continue
        if cone_name == "prefix-aggregate":
            original = inputs.git(seed["source_revision"], old["source_path"])
            first, last = old["current_lines"]; lines = original.splitlines(keepends=True)
            body = b"".join(lines[first-1:last]); offset = sum(map(len, lines[:first-1]))
            if sha(body) != old["source_text_sha256"]: body = body.rstrip(b"\n")
            assert sha(body) == old["source_text_sha256"]
            correspond(old, body, original, offset, offset+len(body), {"source_cut_signature_sha256": sha(body.split(b"{", 1)[0])})
            continue
        cone = cones[cone_name]; item = cone.item(old["kind"], old["id"])
        if item is None: raise ValueError("Seed LLBC identity absent: " + str(old))
        path, original, body, start, end = cone.source(item)
        assert body is not None and sha(body) == old["source_text_sha256"], (cone_name, old.get("name"))
        correspond(old, body, original, start, end, cone.signatures(old["kind"], old["id"]))

    # The accepted Prefix aggregate retained generated Types/Funs but not its
    # final LLBC. Enumerate EVERY emitted r1_wire declaration, including derives
    # and loop auxiliaries, instead of treating28 source cuts as28 Lean names.
    prefix_kit_path = BASE + "/tools/prefix-aggregate-extraction-kit/"
    prefix_pins = inputs.json(prefix_kit_path + "source-pins.json")
    prefix_lib = inputs.read(prefix_kit_path + "lib.rs")
    layouts = []
    for cut in prefix_pins["declaration_cuts"]:
        original = inputs.git(seed["source_revision"], cut["path"])
        lines = original.splitlines(keepends=True)
        body = b"".join(lines[cut["first_line"]-1:cut["last_line"]])
        if sha(body) != cut["sha256"]: body = body.rstrip(b"\n")
        assert sha(body) == cut["sha256"]
        at = prefix_lib.find(body)
        if at < 0: raise ValueError("Prefix source cut missing from exact kit: " + cut["name"])
        layouts.append((at, at+len(body), cut, body, original,
                        sum(map(len, lines[:cut["first_line"]-1]))))
    for file in ["Types.lean", "Funs.lean"]:
        path = BASE + "/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/" + file
        raw = inputs.read(path); text = raw.decode(); declarations = lean_declarations(raw)
        for name, emitted in declarations.items():
            if not name.startswith("r1_wire."): continue
            occurrence = re.search(r"\b(?:def|structure|inductive|abbrev|impl_def)\s+" + re.escape(name) + r"(?=\s|:|$)", text)
            if occurrence is None:
                unresolved.append({"cone": "prefix-emitted", "name": name, "reason": "Generated declaration location missing"}); continue
            doc_start = text.rfind("/--", 0, occurrence.start())
            comment = text[doc_start:occurrence.start()]
            location = re.search(r"Source: 'lib.rs', lines (\d+):(\d+)-(\d+):(\d+)", comment)
            candidates = []
            if location:
                start = positions(prefix_lib)[int(location[1])-1] + int(location[2])
                candidates = [q for q in layouts if q[0] <= start < q[1]]
            if not candidates:
                # Aeneas loop metadata can span line1..function-end. Name the
                # exact retained parent Rust function instead of guessing line1.
                base_name = re.sub(r"_loop\d*(?:\.body)?$", "", name).split(".")[-1]
                candidates = [q for q in layouts if re.search(rb"\bfn\s+" + base_name.encode() + rb"(?:\s|[<(])", q[3])]
            if len(candidates) != 1:
                unresolved.append({"cone": "prefix-emitted", "name": name, "reason": "Generated declaration has no unique retained Rust cut", "candidate_cuts": [q[2]["name"] for q in candidates]}); continue
            _, _, cut, body, original, offset = candidates[0]
            if cut["path"] not in current: continue
            correspond({"cone": "prefix-emitted", "kind": "generated-declaration", "name": name,
                "source_path": cut["path"], "cut": cut["name"]}, body, original, offset, offset+len(body),
                {"generated": [{"lean_name": "AspisR1PrefixAggregateParser." + name,
                    "lean_file": path, **{k: emitted[k] for k in ["body_sha256", "signature", "signature_sha256"]}}]})

    # B's current emitted pure helper. SDK declarations/constructors are retained
    # separately below, since their SDK files were not migration-changed sources.
    b_spec = {"cone": "metadata-current", "archive": BASE + "/evidence/readonly-buffer-20261016/readonly-buffer-evidence.tar.gz", "llbc_member": "extraction/ReadonlyBufferMeta.llbc", "kit": "readonly-meta-extraction-kit/source-pins.json"}
    bcone = archive_cone(b_spec, inputs)
    for item in bcone.data["fun_decls"]:
        if not item or item["item_meta"]["name"][-1].get("Ident", [""])[0] != "readonly_buffer_meta_ok": continue
        _, original, body, start, end = bcone.source(item)
        correspond({"cone": "metadata-current", "kind": "fun_decls", "id": item["def_id"], "name": item["item_meta"]["name"], "source_path": "programs/r1-cost-probe/src/r1_pool_adapter.rs"}, body, original, start, end, bcone.signatures("fun_decls", item["def_id"]), fresh=True)

    # Current A52 caller/opening cone. Resolve Rust source membership by exact
    # historical cut layout BEFORE looking at current body text.
    a_prefix = BASE + "/evidence/digest32-worker-a-checkpoint-20261016"
    a_archive_path = a_prefix + "/worker-a-checkpoint.tar.gz"
    a_archive = inputs.read(a_archive_path, optional=True)
    a_llbc = None; a_original_audit = None
    current_a = None
    if a_archive is not None:
        with tarfile.open(fileobj=io.BytesIO(a_archive)) as tf:
            a_llbc = tf.extractfile("c16/PublicPreparation.llbc").read()
            kit = json.load(tf.extractfile("c16/input/source-pins.json"))
            a_original_audit = json.load(tf.extractfile("c16/lean/original-declaration-audit.json"))
            files = {"PublicPreparation.llbc": a_llbc}
            for name in ["translation.json", "AspisR1PublicPreparation/Types.lean", "AspisR1PublicPreparation/Funs.lean"]:
                files["generated/" + name] = tf.extractfile("c16/generated/" + name).read()
        assert kit == inputs.json(BASE + "/tools/digest32-callers-extraction-kit/source-pins.json")
        current_a = Cone("current-callers", files, "PublicPreparation.llbc", kit, inputs)
        for kind in KINDS:
            for item in current_a.data[kind]:
                if not item: continue
                path, original, body, start, end = current_a.source(item)
                if path != "lib.rs" or original is None or start is None: continue
                containing = [q for q in kit["layout_spans"] if q["start_byte"] <= start < q["end_byte_exclusive"]]
                if not containing:
                    synthetic.append({"cone": "current-callers", "kind": kind, "id": item["def_id"], "name": item["item_meta"]["name"], "source_path": path, "reason": "Kit-only declaration outside every historical production cut", "signature": current_a.signatures(kind, item["def_id"])})
                    continue
                assert len(containing) == 1
                cut = next(q for q in kit["cuts"] if q["name"] == containing[0]["name"])
                target = cut["path"]
                if target not in current: continue
                correspond({"cone": "current-callers", "kind": kind, "id": item["def_id"], "name": item["item_meta"]["name"], "source_path": target, "cut": cut["name"]}, body, original, start, end, current_a.signatures(kind, item["def_id"]), fresh=True)
    else:
        unresolved.append({"cone": "current-callers", "reason": "Current accepted caller cone absent at ref/supplements"})

    additional = []; additional_exclusions = collections.Counter(); followup_layouts = []; followup_specs = []
    builtin = [
        {"cone": "accepted-prepared-actual", "archive": BASE + "/evidence/prepared-actual-20261016/actual-prepared-evidence.tar.gz",
         "llbc_member": "VerifyPreparedPrefix.llbc", "accepted_prefix": "generated/", "kit": "prepared-actual-extraction-kit/input/source-pins.json",
         "binding_audits": [BASE + "/lean/bridge-prepared-3335-20261016/binding-pins.json"],
         "bound_models": [BASE + "/lean/bridge-prepared-3335-20261016/ExtractedPreparedModel.lean"]},
        {"cone": "accepted-tx1-actual-accumulator", "archive": BASE + "/evidence/tx1-caller-accepted-20261016/tx1-caller-accepted.tar.gz",
         "llbc_member": "tx1-actual-accumulator/VerifyPreparedPrefix.llbc", "accepted_prefix": "tx1-actual-accumulator/", "kit": "tx1-caller-extraction-kit/input-accumulator/source-pins.json",
         "binding_audits": [BASE + "/lean/bridge-tx1-e5c186ba3-20261016/" + p for p in ["tx1-binding-pins.json", "prepared-binding-pins.json", "common-funs-audit.json", "union-pins.json"]],
         "bound_models": [BASE + "/lean/bridge-tx1-e5c186ba3-20261016/ExtractedTx1Model.lean", BASE + "/lean/bridge-tx1-e5c186ba3-20261016/ExtractedPreparedModel.lean"]}]
    # The first prefix selects generated text while retaining the separately
    # named accepted LLBC. Both are explicit, never first-translation guessing.
    specs = []
    for spec in builtin:
        if inputs.read(spec["archive"], optional=True) is not None: specs.append(spec)
    for path in args.additional_cone:
        manifest = inputs.json(path)
        specs.extend(manifest if isinstance(manifest, list) else manifest.get("cones", [manifest]))
    for cone_spec in specs:
        cone = archive_cone(cone_spec, inputs); additional.append(cone); followup_specs.append(cone_spec)
        layout = []; lib = None
        if cone.kit.get("base52_cuts"):
            lib, layout, layout_audit = verified_fragment_layout(cone, cone_spec, inputs)
            followup_layouts.append(layout_audit)
        for kind in KINDS:
            for item in cone.data[kind]:
                if not item: continue
                source, original, body, start, end = cone.source(item)
                targets = [p for p in current if source == p or source.endswith("/" + p)]
                mapped = None; provenance = "direct LLBC production source path"
                if layout:
                    # Rust compiler-generated metadata may point into core but
                    # retain the originating production declaration source_text.
                    candidates = []
                    if source == "lib.rs" and start is not None:
                        candidates = [q for q in layout if q["start_byte"] <= start and end <= q["end_byte_exclusive"]]
                    elif body is not None and str(item["item_meta"]["name"][0]).find("aspis_r1_") >= 0:
                        for hit in re.finditer(re.escape(body), lib):
                            candidates += [dict(q, recovered_start=hit.start()) for q in layout
                                if q["start_byte"] <= hit.start() and hit.end() <= q["end_byte_exclusive"]]
                        if candidates:
                            starts = {q["recovered_start"] for q in candidates}
                            if len(starts) == 1:
                                start = next(iter(starts)); end = start + len(body); original = lib
                                provenance = "Compiler-origin metadata mapped by exact retained source_text to one verified production cut"
                    identities = {(q["path"], q["source_revision"], q["source_start_byte"], q["name"]) for q in candidates}
                    if len(identities) == 1:
                        mapped = candidates[0]; targets = [mapped["path"]] if mapped["path"] in current else []
                    elif source == "lib.rs" or candidates:
                        signature = cone.signatures(kind, item["def_id"])
                        entry = {"cone": cone.name, "kind": kind, "id": item["def_id"], "name": item["item_meta"]["name"],
                            "source_path": source, "source_text_sha256": sha(body) if body is not None else None,
                            "reason": "Kit-only/opaque stub outside verified production cuts" if not candidates else "Ambiguous production cut mapping",
                            "signature": signature, "not_accepted_as_production_body": True}
                        if candidates: unresolved.append(entry)
                        else: synthetic.append(entry)
                        continue
                elif source == "lib.rs":
                    containing = [q for q in cone.kit.get("layout_spans", [])
                        if q.get("start_byte", q.get("byte_start", -1)) <= (start if start is not None else -2)
                        < q.get("end_byte_exclusive", q.get("byte_end_exclusive", -1))]
                    if len(containing) == 1:
                        cut = next(q for q in cone.kit["cuts"] if q["name"] == containing[0]["name"])
                        targets = [cut["path"]] if cut["path"] in current else []
                    else:
                        unresolved.append({"cone": cone.name, "kind": kind, "id": item["def_id"],
                            "name": item["item_meta"]["name"], "reason": "lib.rs declaration has no unique historical production layout mapping"}); continue
                if not targets:
                    additional_exclusions[cone.name + ":" + source + (":" + mapped["path"] if mapped else "")] += 1
                    continue
                signature = cone.signatures(kind, item["def_id"])
                opaque = any(q.get("is_opaque") for q in signature["generated"]) or item.get("body") == "Opaque"
                for target in targets:
                    correspond({"cone": cone.name, "kind": kind, "id": item["def_id"],
                        "name": item["item_meta"]["name"], "source_path": target,
                        "source_mapping": mapped, "source_mapping_basis": provenance,
                        "emission_kind": "opaque-boundary-signature-only" if opaque else "emitted-body-or-type" if signature["generated"] else "retained-LLBC-metadata-only",
                        "actual_body_emitted": bool(signature["generated"]) and not opaque,
                        "boundary_implementation_unproved": opaque},
                        body, original, start, end, signature, fresh=True)
    # C's original79 naming-only audit: check every token hash against raw current
    # generated declarations, including attributes and atomic string contents.
    c_path = BASE + "/lean/bridge-public-callers-c16-20261016/adapter-pins.json"
    c = inputs.json(c_path); naming = []
    if a_original_audit is not None: assert c == a_original_audit, "A committed original79 audit must match C overlay"
    if current_a:
        for file, audit_file in c["declarations"].items():
            raw = current_a.files["generated/AspisR1PublicPreparation/" + file]
            assert sha(raw) == audit_file["current_raw_sha256"]
            parsed = lean_declarations(raw)
            for entry in audit_file["unchanged_declarations"]:
                name = entry["declaration"]
                if name not in parsed or parsed[name]["body_sha256"] != entry["token_sha256"]:
                    unresolved.append({"name": name, "reason": "C79 token identity missing/mismatch"})
                naming.append({**entry, "file": file, "generated_signature_sha256": parsed.get(name, {}).get("signature_sha256"), "enclosing_generated_namespace": "AspisR1PublicPreparation"})
        assert len(naming) == 79
        original79 = {q["declaration"]: q for q in naming}
        for row in rows:
            if row["cone"] != "current-callers" or row["classification"] == "unresolved": continue
            generated = row["retained_signature"]["generated"]
            if generated and all(q["lean_name"].split(".", 1)[-1] in original79 for q in generated):
                row["classification"] = "unchanged"
                row["C79_original_token_identity"] = [original79[q["lean_name"].split(".", 1)[-1]] for q in generated]
                row.pop("previous_statement_status", None); row["statement_diff"] = ""
        # Generated loop helpers are distinct Lean declarations even when one
        # LLBC function owns all of them. Inventory them independently.
        named = {q["lean_name"].split(".", 1)[-1] for row in rows
                 for q in row.get("retained_signature", {}).get("generated", [])}
        for file, audit_file in c["declarations"].items():
            parsed = lean_declarations(current_a.files["generated/AspisR1PublicPreparation/" + file])
            for name in audit_file["new_declarations"]:
                if name in named: continue
                parent = re.sub(r"_loop\d*(?:\.body)?$", "", name)
                parents = [row for row in rows if row["cone"] == "current-callers" and any(
                    q["lean_name"].split(".", 1)[-1] == parent for q in row["retained_signature"]["generated"])]
                if len(parents) != 1:
                    # Non-migration source helpers need no current-source row;
                    # keep their emitted metadata as an explicit exclusion.
                    synthetic.append({"cone": "current-callers", "name": name,
                        "reason": "No migration-changed parent in current rows; generated metadata retained", "generated": parsed[name]})
                    continue
                row = dict(parents[0]); emitted = parsed[name]
                row.update(name=name, kind="generated-loop-auxiliary", classification="re-extracted",
                    retained_signature={"generated": [{"lean_name": "AspisR1PublicPreparation." + name,
                        **{k: emitted[k] for k in ["body_sha256", "signature", "signature_sha256"]}}]},
                    statement_diff=statement_diff("", emitted["signature"]),
                    previous_statement_status="New generated loop auxiliary of the named exact Rust parent")
                rows.append(row)

    # C's accepted first CONTROL-FLOW interpretation has explicitly generalized
    # carriers/opaque continuations. It is never a concrete SDK/tx1 extraction.
    first_pins = inputs.json(BASE + "/tools/public-binding-followup-kit/first-diagnostic-input/source-pins.json")
    first_audit = inputs.json(BASE + "/evidence/public-binding-followup-20261016/first-binder-audit.json")
    first_generated_path = BASE + "/evidence/public-binding-followup-20261016/generated-extended/AspisR1FirstDiagnostic/Funs.lean"
    first_generated_raw = inputs.read(first_generated_path)
    assert sha(first_generated_raw) == first_audit["generated_funs_sha256"]
    first_generated = lean_declarations(first_generated_raw)["first"]
    first_bound_raw = inputs.read(first_audit["bound_model_source"])
    assert sha(first_bound_raw) == first_audit["bound_model_sha256"]
    first_bound_text = first_bound_raw.decode()
    first_bound_start = first_bound_text.index("def first ")
    first_bound_end = first_bound_text.index("\nprivate theorem", first_bound_start)
    first_bound_tokens = lean_tokens(first_bound_text[first_bound_start:first_bound_end])
    first_bound_signature_tokens = first_bound_tokens[:first_bound_tokens.index(":=")]
    source = first_pins["source"]; first_source = inputs.git(first_pins["revision"], source)
    first_start, first_end = first_pins["first"]["start_byte"], first_pins["first"]["end_byte_exclusive"]
    first_body = first_source[first_start:first_end]; assert sha(first_body) == first_pins["first"]["sha256"]
    correspond({"cone": "C-first-boundary-interpretation", "kind": "function", "name": "first", "source_path": source,
        "actual_concrete_SDK_or_tx1_carriers_emitted": False, "boundary_audit": first_audit,
        "diagnostic_generated_declaration": {"file": first_generated_path,
            **{k: first_generated[k] for k in ["body_sha256", "signature", "signature_sha256"]}},
        "boundary_statement_diff": statement_diff(first_audit["generated_signature"], first_audit["parametric_signature"])},
        first_body, first_source, first_start, first_end,
        {"generated": [{"lean_name": "AspisR1PublicPreparation.FirstCaller.first",
            "signature": first_audit["parametric_signature"],
            "signature_sha256": sha(canonical(first_bound_signature_tokens)),
            "body_sha256": sha(canonical(first_bound_tokens)),
            "enclosing_generated_namespace": "AspisR1PublicPreparation.FirstCaller",
            "lean_file": first_audit["bound_model_source"]}]}, fresh=True)
    b_inventory = inputs.json(BASE + "/evidence/readonly-buffer-20261016/re-pin-inventory.json")
    b_generated = {}
    for file_pin in b_inventory["files"]:
        raw = inputs.read(file_pin["path"])
        assert sha(raw) == file_pin["current_sha256"], "B generated output changed: " + file_pin["path"]
        b_generated[file_pin["path"]] = (raw, lean_declarations(raw))
    b_current = []
    for declaration in b_inventory["declarations"]:
        raw, parsed = b_generated[declaration["path"]]
        name = declaration["name"].split(".", 1)[-1]
        if declaration.get("kind") == "constructor":
            line = declaration["statement"] + "\n"
            assert line.encode() in raw and sha(line.encode()) == declaration["declaration_sha256"]
            emitted = {"body_sha256": sha(canonical(lean_tokens(line))),
                       "signature_sha256": sha(canonical(lean_tokens(line)))}
        else:
            assert name in parsed, "B generated declaration missing: " + name
            emitted = {k: parsed[name][k] for k in ["body_sha256", "signature_sha256"]}
        b_current.append({**declaration, "checked_target_revision": ref,
            "current_generated_file_sha256": sha(raw), **emitted,
            "enclosing_generated_namespace": "AspisR1ReadonlyMeta"})
    begin_diff = inputs.json(a_prefix + "/begin-re-extraction-statement-diff.json")
    for row in rows:
        if row["cone"] == "current-callers" and any(q["lean_name"].endswith(".r1_wire.begin") for q in row.get("retained_signature", {}).get("generated", [])):
            row["actual_begin_re_extraction_diff"] = begin_diff

    reconcile_followup_statements(rows, [*cones.values(), *([current_a] if current_a else []), *additional], {q.name for q in additional})

    # Preserve the broader historical scan as metadata, not as accepted status.
    baseline_scan = inputs.json(BASE + "/evidence/begin-straightline-native-20261016/re-pin-coverage-review.json")
    coverage = collections.Counter(q["source_path"] for q in rows)
    result = {"source_revision": ref, "migration_before": before,
        "scope": "Enumerated retained accepted/current cones from A's explicit LLBC membership registry, current A52, B helper/SDK inventory, C79 naming audit, accepted Prefix cuts, actual Prepared and accepted tx1/Accumulator emissions. Only explicit accepted prefixes selected. Historical/diagnostic/opaque-stub bodies are not promoted to source theorems. No source/runtime refinement theorem is claimed.",
        "original_registered_cone_counts": dict(collections.Counter(q["classification"] for q in rows if q["cone"] not in {v.name for v in additional})),
        "followup_registered_cone_counts": dict(collections.Counter(q["classification"] for q in rows if q["cone"] in {v.name for v in additional})),
        "followup_emission_kinds": dict(collections.Counter(q.get("emission_kind") for q in rows if q["cone"] in {v.name for v in additional})),
        "followup_source_inventory_status": "Current accepted cuts include verifier.rs, the actual query body and complete verify_finish. Per-binding audits list each remaining arithmetic/allocation/sampler/conversion API explicitly. Rejected diagnostic emissions remain historical, never source-body theorems.",
        "inventory_gate": "OPEN: unresolved correspondence" if unresolved else "PASS for enumerated accepted/current universe; lead owns final universe/merge review",
        "classification_counts": dict(collections.Counter(q["classification"] for q in rows)),
        "declarations": rows, "unresolved": unresolved, "synthetic_kit_declarations": synthetic,
        "C79_generated_naming_overlay": naming, "B_generated_declaration_inventory": b_inventory,
        "B_current_generated_declarations": b_current,
        "historical_universe_scan": baseline_scan["scan"],
        "historical_universe_scan_scope": baseline_scan["scan_scope"],
        "historical_universe_index": history_index(inputs, [*cones.values(), bcone, *([current_a] if current_a else []), *additional], changed),
        "aliases_and_experiments": baseline_scan["alias_disambiguation"],
        "frozen_import_scope": baseline_scan["frozen_import_audit"],
        "source_context_limit": "Lexical source/context identity plus retained generated/LLBC signature hashes is not current compiler name resolution. Type/body substitutions or changed containers remain explicit unresolved or re-extracted entries; no current-text membership filter silently removes them.",
        "deleted_production_source_files": sorted(set(changed)-set(current)),
        "file_coverage": [{"source_path": p, "source_sha256": sha(raw),
            "changed_since_migration_before": p in changed,
            "inventory_entries": coverage[p],
            "meaning": ("Retained accepted source outside the selected migration diff; correspondence still checked" if p not in changed else
                        "No declaration in enumerated retained accepted/current cones" if not coverage[p] else "")}
            for p, raw in current.items()],
        "accepted_cones": [q.archive_pin for q in [*cones.values(), bcone, *additional]],
        "current_A_callers_cone": {"archive": a_archive_path, "archive_sha256": sha(a_archive) if a_archive is not None else None,
            "llbc_member": "c16/PublicPreparation.llbc",
            "llbc_sha256": sha(a_llbc) if a_llbc is not None else None,
            "layout_pin_member": "c16/input/source-pins.json",
            "declaration_counts": {k: sum(x is not None for x in current_a.data[k]) for k in KINDS} if current_a else {}},
        "additional_nonmigration_source_exclusions": dict(additional_exclusions),
        "followup_verified_fragment_layouts": followup_layouts,
        "followup_explicit_accepted_specs": followup_specs,
        "followup_binding_and_model_audits": bound_statement_audits(inputs, followup_specs, additional),
        "inputs": inputs.pins, "script_sha256": sha(Path(__file__).read_bytes()),
        "no_builds_Lean_runtime_or_SBF": True}
    encoded = (json.dumps(result, indent=2, sort_keys=True) + "\n").encode()
    if args.check: assert args.output.read_bytes() == encoded
    else: args.output.parent.mkdir(parents=True, exist_ok=True); args.output.write_bytes(encoded)
    print(json.dumps({"inventory_gate": result["inventory_gate"], "counts": result["classification_counts"], "unresolved": len(unresolved), "C79": len(naming), "output_sha256": sha(encoded)}, sort_keys=True))
    if args.require_complete and unresolved: raise SystemExit(2)


if __name__ == "__main__":
    main()
