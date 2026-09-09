#!/usr/bin/env python3
"""Read-only evidence audit; never builds, replays, enumerates fields or transfers.

Incomplete evidence is emitted as an explicitly pending inventory with exit 1.
Only a complete current-source inventory may be checked against the recorded
manifest. Linux output paths require a hash-checked transfer receipt; unavailable
remote artifacts are not silently treated as verified local cache entries.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import re
import sys

from audit_soundness_proofs import ALLOWED

EX = Path(__file__).resolve().parent
RD = EX.parent
BASE = "b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
MATHLIB = "81a5d257c8e410db227a6665ed08f64fea08e997"
LEAN = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
LEAVES = {
    "FoldSupportClosure": "fold-support-closure",
    "HighAgreementTail": "high-agreement-tail",
    "MaskedCurveTail": "masked-curve-tail",
    "OffFamilyIntersection": "off-family-intersection",
    "MaskedCurveRepresentation": "masked-curve-representation",
    "SelectedMaskedCurveTail": "selected-masked-curve-tail",
    "TwoTailQueryBound": "two-tail-query-bound",
    "SelectedOutsideQuery": "selected-outside-query",
    "FixedC1OutsideQuery": "fixed-c1-outside-query",
    "SelectedSupportIdentification": "selected-support-identification",
}
BAD_LOG = r"sorryAx|: error:|^error:|memory_exception|AGGREGATE_RSS_STOP|PROVENANCE_CHANGED"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def relative(path):
    try:
        return str(path.relative_to(RD))
    except ValueError:
        return str(path)


def measurements(log):
    """Normalize GNU maximum RSS (KiB) and Darwin maximum RSS (bytes)."""
    darwin = re.findall(r"^\s*([0-9.]+) real", log, re.M)
    gnu = re.findall(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)", log)
    require(not (darwin and gnu), "mixed time formats in one stage log")
    if darwin:
        rss = re.findall(r"^\s*(\d+)\s+maximum resident set size", log, re.M)
        swaps = re.findall(r"^\s*(\d+)\s+swaps$", log, re.M)
        times = list(map(float, darwin))
        multiplier, platform = 1, "Darwin_time_l"
    else:
        rss = re.findall(r"Maximum resident set size \(kbytes\):\s*(\d+)", log)
        swaps = re.findall(r"^\s*Swaps:\s*(\d+)\s*$", log, re.M)
        times = []
        for value in gnu:
            total = 0.0
            for part in value.split(":"):
                total = total * 60 + float(part)
            times.append(total)
        multiplier, platform = 1024, "GNU_time_v"
    require(times and len(times) == len(rss) == len(swaps), "missing/incomplete resource block")
    require(all(int(value) == 0 for value in swaps), "nonzero recorded swaps")
    return [{"wall_seconds": wall, "peak_rss_bytes": int(memory)*multiplier,
             "swaps": int(swap), "format": platform}
            for wall, memory, swap in zip(times, rss, swaps)]


def axiom_audits(source, log):
    requested = re.findall(r"^#print axioms\s+([\w.]+)\s*$", source, re.M)
    require(requested, "no named axiom audits in source")
    result = []
    for declaration, raw in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S):
        used = {value.strip() for value in raw.split(",") if value.strip()}
        require(used <= ALLOWED, f"nonstandard axioms: {declaration}: {sorted(used)}")
        result.append({"declaration": declaration, "axioms": sorted(used)})
    result.extend({"declaration": name, "axioms": []}
                  for name in re.findall(r"'([^']+)' does not depend on any axioms", log))
    require(len(result) == len(requested), "axiom audit count differs from current source")
    for name in requested:
        require(sum(row["declaration"] == name or row["declaration"].endswith("."+name)
                    for row in result) == 1, f"missing/ambiguous audit: {name}")
    return result


class Transfer:
    """Optional receipt. Every remote pathname must map to exact local bytes.

    Expected receipt keys: research, borrowed, mathlib, lean_commit, manifest
    {path,sha256}, artifacts [{remote_path,local_path,sha256}], runs
    [{target,log,command,memory_high_bytes,memory_max_bytes,memory_swap_max}].
    Paths in receipt are absolute or relative to the receipt's directory.
    """
    def __init__(self, path):
        self.path, self.data, self.artifacts, self.manifest = path, None, {}, None
        if path is None or not path.exists():
            return
        data = json.loads(path.read_text())
        for key, expected in (("research", BASE), ("borrowed", BORROWED),
                              ("mathlib", MATHLIB), ("lean_commit", LEAN)):
            require(data.get(key) == expected, f"transfer pin mismatch: {key}")
        manifest = self.resolve(data["manifest"]["path"])
        require(sha(manifest) == data["manifest"]["sha256"], "transfer manifest hash mismatch")
        contents = json.loads(manifest.read_text())
        for key in ("research", "borrowed", "mathlib", "lean_commit"):
            require(contents.get(key) == data[key], f"staged manifest pin mismatch: {key}")
        self.manifest = contents
        for entry in data["artifacts"]:
            local = self.resolve(entry["local_path"])
            require(re.fullmatch(r"[a-f0-9]{64}", entry["sha256"]), "malformed artifact digest")
            key = (entry["remote_path"], entry["sha256"])
            require(key not in self.artifacts, "duplicate remote artifact version")
            # Different jobs can use different snapshots at one remote path.
            # Verify bytes lazily when a successful log actually imports them;
            # unrelated pending-source edits do not invalidate an earlier leaf.
            self.artifacts[key] = local
        self.data = data

    def resolve(self, path):
        path = Path(path)
        return path if path.is_absolute() else self.path.parent / path

    def file(self, raw, expected):
        path = Path(raw)
        if (raw, expected) in self.artifacts:
            local = self.artifacts[(raw, expected)]
            require(sha(local) == expected, f"transferred artifact mismatch: {local}")
            return local
        require(path.exists(), f"unavailable logged artifact with no transfer receipt: {raw}")
        require(sha(path) == expected, f"logged current artifact hash mismatch: {raw}")
        return path

    def runs(self, target):
        return [] if self.data is None else [row for row in self.data["runs"] if row["target"] == target]


def remote_closure(name, log, hashes, transfer):
    manifests = [(value, raw) for value, raw in hashes if Path(raw).name.endswith("-manifest.json")]
    require(len(manifests) == 1, "missing unique run-specific import manifest")
    manifest_hash, raw = manifests[0]
    manifest = json.loads(transfer.file(raw, manifest_hash).read_text())
    for key, expected in (("research", BASE), ("borrowed", BORROWED),
                          ("mathlib", MATHLIB), ("lean_commit", LEAN)):
        require(manifest.get(key) == expected, f"run manifest pin mismatch: {key}")
    require(manifest["packages"].get("mathlib") == MATHLIB, "missing native Mathlib package pin")
    require(manifest["packages"] == transfer.manifest["packages"], "native package pins changed between runs")
    counts = re.findall(r"^OVERLAY_PROVENANCE_PASS=(\d+)\s*$", log, re.M)
    require(counts == [str(len(manifest["files"]))]*2, "run manifest pre/post checks incomplete")
    require("PROVENANCE_UNCHANGED=true" in log and
            "NATIVE_PACKAGE_CACHE_BOUNDARY=pinned revisions; not a replay of package compilation" in log,
            "missing remote/native-cache boundary postflight")
    task = re.search(r"^REMOTE_TASK=(.+)$", log, re.M)
    require(task is not None, "missing remote task identity")
    modules = {}
    for entry in manifest["files"]:
        modules.setdefault(entry["module"], []).append(entry)
    # Only the actual imported closure is required to remain available. The
    # initial archive may also contain later PENDING targets that change.
    pending, seen, native, verified = [name], set(), set(), 0
    native_roots = {"Mathlib", "Plausible", "LeanSearchClient", "ImportGraph",
                    "ProofWidgets", "Aesop", "Qq", "Batteries", "Cli"}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        if module.split(".")[0] in {"Init", "Std", "Lean", "Lake"}:
            continue
        if module not in modules:
            require(module.split(".")[0] in native_roots, f"unrecorded nonpackage import: {module}")
            native.add(module)
            continue
        entries = modules[module]
        sources = [entry for entry in entries if entry["kind"] == "source"]
        require(len(sources) == 1, f"missing/ambiguous imported source: {module}")
        if module == name:
            require(sources[0]["sha256"] == sha(EX/(name+".lean")), "run manifest target differs from current source")
        if module != name:
            require(sum(entry["kind"] == "olean" for entry in entries) == 1,
                    f"newly compiled import absent from versioned manifest: {module}")
        source_path = None
        for entry in entries:
            raw_entry = task.group(1)+"/overlay/"+entry["overlay"]
            key = (raw_entry, entry["sha256"])
            if key not in transfer.artifacts and entry.get("local"):
                local = Path(entry["local"])
                require(sha(local) == entry["sha256"], f"imported initial local snapshot changed: {local}")
            else:
                local = transfer.file(raw_entry, entry["sha256"])
            verified += 1
            if entry["kind"] == "source":
                source_path = local
        # Selected/research source imports are literal one-module lines. Skip
        # commented imports, including nested block comments, before scanning.
        data = source_path.read_text()
        clean, depth, i = [], 0, 0
        while i < len(data):
            pair = data[i:i+2]
            if pair == "/-":
                depth += 1; i += 2
            elif depth and pair == "-/":
                depth -= 1; i += 2
            elif depth:
                clean.append("\n" if data[i] == "\n" else " "); i += 1
            elif pair == "--":
                while i < len(data) and data[i] != "\n": i += 1
            elif data[i] == '"':
                clean.append(" "); i += 1
                while i < len(data):
                    if data[i] == "\\":
                        i += 2
                    elif data[i] == '"':
                        i += 1; break
                    else:
                        clean.append("\n" if data[i] == "\n" else " "); i += 1
            else:
                clean.append(data[i]); i += 1
        pending.extend(re.findall(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)",
                                  "".join(clean), re.M))
    return {"manifest_sha256": manifest_hash, "manifest_entries": len(manifest["files"]),
            "actual_import_artifacts_verified": verified, "native_package_imports": sorted(native),
            "native_package_revisions": manifest["packages"],
            "native_package_cache_boundary": "pinned revisions, not a package build replay"}


def check_leaf(name, path, transfer):
    source_path = EX / (name+".lean")
    source, digest, log = source_path.read_text(), sha(source_path), path.read_text()
    require(not re.search(BAD_LOG, log, re.M), "diagnostic/error/guard marker in log")
    require(re.findall(r"^LEAN_EXIT=(\d+)\s*$", log, re.M) == ["0"], "missing or nonzero terminal LEAN_EXIT")
    require(BASE in log and BORROWED in log and LEAN in log, "missing source/toolchain pins")
    require(not re.search(r"^\s*(axiom|sorry|admit)\b|\bby\s+(sorry|admit)\b", source, re.M),
            "admitted/new-axiom source declaration")
    hashes = re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M)
    targets = [(value, raw) for value, raw in hashes if Path(raw).name == name+".lean"]
    require(targets and all(value == digest for value, _ in targets), "no current-source target hash")
    outputs = [(value, raw) for value, raw in hashes if Path(raw).name == name+".olean"]
    require(outputs and len({value for value, _ in outputs}) == 1, "missing/ambiguous output olean hash")
    resources = measurements(log)
    require(len(resources) == 1, "expected one focused Lean invocation")
    remote = resources[0]["format"] == "GNU_time_v"
    if remote:
        candidates = [row for row in transfer.runs(name) if transfer.resolve(row["log"]) == path]
        require(len(candidates) == 1, "GNU log has no unique transfer/run receipt")
        run = candidates[0]
        require(run["memory_swap_max"] == 0, "remote swap is not disabled")
        require(0 < run["memory_high_bytes"] <= run["memory_max_bytes"], "invalid remote cgroup limits")
        profiles = {(5*1024**3, 7*1024**3): "-M6500"}
        changed_import_exception = name in {"SelectedSupportIdentification", "OffFamilyIntersection"}
        if name in {"SelectedMaskedCurveTail", "SelectedOutsideQuery", "FixedC1OutsideQuery"} or changed_import_exception:
            # Parent-authorized first selected cached-composition checks; not
            # an unchanged larger-cap retry of a failed generic declaration.
            profiles[(8*1024**3, 10*1024**3)] = "-M9500"
        limits = (run["memory_high_bytes"], run["memory_max_bytes"])
        require(limits in profiles, "unapproved remote resource profile for this target")
        resource_reason = "original_bounded_profile"
        if limits[1] == 10*1024**3:
            resource_reason = "authorized_first_selected_cached_composition"
            if changed_import_exception:
                changed_predecessors = []
                for previous in EX.glob(LEAVES[name]+"-*.log"):
                    old = previous.read_text()
                    if "memory.max=7516192768" not in old or not re.search(
                            r"memory_exception|AGGREGATE_RSS_STOP|LEAN_EXIT=134", old):
                        continue
                    old_hashes = {value for value, raw in
                                  re.findall(r"^([a-f0-9]{64})  (.+)$", old, re.M)
                                  if Path(raw).name == name+".lean"}
                    require(digest not in old_hashes, "unchanged source retried at larger memory cap")
                    if old_hashes:
                        changed_predecessors.append({"log": relative(previous),
                                                     "source_hashes": sorted(old_hashes)})
                require(changed_predecessors, "changed-import resource exception lacks failed predecessor evidence")
                resource_reason = {"authorization": "parent-authorized changed narrow import closure",
                                   "change": "canonical-schedule-only geometric helper and dependent OffFamily; no larger-than-10GiB job",
                                   "source_sha256": digest, "failed_lower_cap_predecessors": changed_predecessors}
        require(resources[0]["peak_rss_bytes"] <= run["memory_max_bytes"], "remote RSS exceeds declared cap")
        require(run["command"] and run["command"] in log, "remote command missing from execution log")
        require(profiles[limits] in run["command"] and "-j1" in run["command"],
                "remote Lean heap/thread limits differ from approved profile")
        for setting, expected in (("memory.high", run["memory_high_bytes"]),
                                  ("memory.max", run["memory_max_bytes"]),
                                  ("memory.swap.max", 0)):
            require(re.findall(r"^"+re.escape(setting)+r"=(\d+)\s*$", log, re.M) == [str(expected)],
                    f"actual remote cgroup property mismatch: {setting}")
        closure = remote_closure(name, log, hashes, transfer)
        closure["resource_profile_reason"] = resource_reason
    else:
        require(resources[0]["peak_rss_bytes"] <= 7*1024**3, "local RSS exceeds 7GiB audit cap")
        # Some focused runners print the complete closure twice rather than
        # adding a Boolean summary marker. Check the actual pre/post sets.
        before, after = log.split("LEAN_EXIT=0", 1)
        def closure_hashes(part):
            return {(value, raw) for value, raw in
                    re.findall(r"^([a-f0-9]{64})  (.+)$", part, re.M)
                    if Path(raw).suffix in (".lean", ".olean")
                    and Path(raw).name not in (name+".lean", name+".olean")}
        pre, post = closure_hashes(before), closure_hashes(after)
        require(pre and pre == post, "missing or changed local closure postflight")
        run = None
        closure = {"source_olean_pre_post_hash_pairs": len(pre)}
    checked = 0
    for expected, raw in hashes:
        # Retained runner bytes are provenance too; they are not silently skipped.
        transfer.file(raw, expected)
        checked += 1
    audits = axiom_audits(source, log)
    return {"log": relative(path), "log_sha256": sha(path), "exit": 0,
            "source_sha256": digest, "olean_sha256": outputs[-1][0],
            "measurement": resources[0], "axiom_audits": audits,
            "logged_artifact_hash_records_verified": checked,
            "import_closure": closure, "transferred_run": run}


def leaves(transfer):
    results = []
    for name, stem in LEAVES.items():
        candidates = set(EX.glob(stem+"-*.log"))
        candidates.update(EX.glob(name+"-*.log"))
        candidates.update(transfer.resolve(row["log"]) for row in transfer.runs(name))
        green, diagnostics = [], []
        for path in sorted(candidates):
            try:
                green.append(check_leaf(name, path, transfer))
            except (OSError, ValueError, KeyError) as error:
                log = path.read_text() if path.exists() else ""
                categories = []
                for label, pattern in (
                    ("source_elaboration", r": error:|^error:"),
                    ("recursion_limit", r"maximum recursion depth"),
                    ("memory_guard", r"AGGREGATE_RSS_STOP|memory_exception|out of memory|oom-kill"),
                    ("time_limit", r"TIMEOUT|timed out|TIME_LIMIT|LEAN_EXIT=124|SIGXCPU"),
                    ("provenance", r"PROVENANCE_CHANGED|PIN_FAILURE|[Pp]rovenance|[Hh]ash mismatch"),
                    ("axiom_audit_rejected", r"sorryAx")):
                    if re.search(pattern, log, re.M):
                        categories.append(label)
                if not categories:
                    categories.append("missing_or_stale_evidence")
                try:
                    resources = measurements(log)
                except ValueError:
                    resources = None
                diagnostics.append({"log": relative(path),
                                    "log_sha256": sha(path) if path.exists() else None,
                                    "status": "retained_diagnostic_not_release_evidence",
                                    "categories": categories,
                                    "recorded_lean_exits": re.findall(r"^LEAN_EXIT=(\d+)\s*$", log, re.M),
                                    "measurements": resources, "reason": str(error)})
        results.append({"target": name+".lean", "status": "green" if green else "pending",
                        "runs": green, "retained_diagnostics": diagnostics})
    return results


def arithmetic():
    script, logpath, record = (EX/"adaptive_tail_budget.py", EX/"adaptive-tail-budget-v1.log",
                               RD/"adaptive-tail-budget.json")
    log = logpath.read_text()
    require(f"SOURCE_SHA256={sha(script)}" in log and f"RESEARCH_PIN={BASE}" in log,
            "exact arithmetic source/pin mismatch")
    require(re.search(r"^SCRIPT_EXIT=0$", log, re.M), "arithmetic did not exit successfully")
    recorded, _ = json.JSONDecoder().raw_decode(log[log.index("{"):])
    require(recorded == json.loads(record.read_text()), "arithmetic JSON/log mismatch")
    k, T, q, a, t, n = (2**31-1)**4, 262144, 22, 9558, 117965, 128
    p = recorded["parameters"]
    require((int(p["field_cardinality"]), p["domain"], p["queries"], p["family_own_support_floor"],
             p["high_threshold"], p["high_forbidden_alpha_count"]) == (k,T,q,a,t,n), "parameter mismatch")
    def rat(value):
        return Fraction(int(value["numerator"]), int(value["denominator"]))
    exact = [Fraction(comb(a-1,q),comb(T,q)),
             Fraction(9396508281246,k)*Fraction(comb(t-1,q),comb(T,q)), Fraction(127,k)]
    require([rat(row["bound"]) for row in recorded["terms"]] == exact, "term rational mismatch")
    require(rat(recorded["off_family_pointwise_ceiling"]) == sum(exact), "pointwise subtotal mismatch")
    suffix = Fraction(q,k-1)+Fraction(18,k)
    require(rat(recorded["shifted_query_and_three_later_repairs"]) == suffix, "suffix mismatch")
    require(rat(recorded["off_family_scalar_suffix_ceiling"]) == sum(exact)+suffix, "composed mismatch")
    require(Fraction(T*comb(57,4),comb(n,4)) == Fraction(30818304,3175) >= a,
            "support averaging certificate mismatch")
    require(recorded["positive_work_credit"] == 0 and recorded["proof_body_bytes"] == 40282,
            "body/work contract changed")
    require(recorded["global_accepted_extraction_bound"] is None and
            recorded["remaining_global_allowance"] is None, "unsupported global result promoted")
    return {"status": "green", "script_sha256": sha(script), "log_sha256": sha(logpath),
            "record_sha256": sha(record), "measurement": measurements(log),
            "independent_check": "exact rational terms and support certificate; no multiset enumeration rerun",
            "result": recorded}


def overlap():
    path = EX/"fork-overlap-control-v1.log"
    log = path.read_text()
    require(BASE in log and "BUILD_EXIT=0" in log and "RUN_EXIT=0" in log, "overlap run/pin failed")
    require(not re.search(BAD_LOG, log, re.M), "overlap error/guard marker")
    for expected, raw in re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M):
        require(sha(Path(raw)) == expected, f"overlap dependency changed: {raw}")
    rows = [json.loads(line) for line in log.splitlines() if line.startswith("{")]
    frozen = [row for row in rows if "frozen_case" in row]
    require(len(frozen) == 8 and sum(row["candidates"] for row in frozen) == 2553,
            "frozen policy census mismatch")
    require(all(row["max_identified"] == 5 and row["overlap_added"] == 0 and
                row["oracle_slot_reads"] == 16 for row in frozen), "frozen closure result mismatch")
    positive = next(row for row in rows if "positive_control" in row)
    require((positive["identified"], positive["observed_intersection"], positive["promoted_mask"],
             positive["actual_full_matching_intersection"], positive["closure_oracle_slot_reads"],
             positive["fullsupport_lookup_total_slot_reads"]) == (7,0,7,7,12,16), "positive control mismatch")
    require(positive["image_residual"] == [0,0] and positive["overlap_added"] == 0,
            "positive control image/closure mismatch")
    negative = next(row for row in rows if "explicit_failure_controls" in row)
    require(negative["explicit_failure_controls"] == 7, "missing named failure controls")
    summary = next(row for row in rows if row.get("mode") == "frozen_policy_overlap_closure")
    require(summary["source_search_rerun"] is False and summary["subsets"] == 2665,
            "scope or interpolation census mismatch")
    resources = measurements(log)
    require(len(resources) == 2 and all(row["peak_rss_bytes"] <= 1024**3 for row in resources),
            "overlap resource contract mismatch")
    return {"status": "green", "log": relative(path), "log_sha256": sha(path),
            "measurements": resources, "frozen": frozen, "positive_control": positive,
            "failure_controls": negative, "summary": summary,
            "scope": "restricted full-oracle cache/observation control, not authenticated replay, payment or QM31 probability"}


def receipt_inventory():
    """Emit, but never write, a receipt for the already transferred artifacts."""
    initial = EX/"masked-nuc-initial-manifest.json"
    manifest = json.loads(initial.read_text())
    artifacts, runs, missing = {}, [], []
    for path in sorted(EX.glob("*-nuc-*.log")):
        log = path.read_text()
        target = re.search(r"^TARGET=(.+)$", log, re.M)
        if target is None:
            continue
        for digest, raw in re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M):
            possible = [EX/Path(raw).name, EX/(path.stem+"-source.txt")]
            local = next((item for item in possible if item.exists() and sha(item) == digest), None)
            if local is None:
                missing.append({"log": relative(path), "remote_path": raw, "sha256": digest})
            else:
                artifacts[(raw,digest)] = {"remote_path": raw, "local_path": relative(local), "sha256": digest}
        command = re.search(r"^COMMAND=(.+)$", log, re.M)
        def prop(name):
            value = re.search(r"^"+re.escape(name)+r"=(\d+)\s*$", log, re.M)
            return int(value.group(1)) if value else None
        runs.append({"target": target.group(1), "log": relative(path),
                     "command": command.group(1) if command else None,
                     "memory_high_bytes": prop("memory.high"), "memory_max_bytes": prop("memory.max"),
                     "memory_swap_max": prop("memory.swap.max")})
    # Generated imported sidecars may occur only in a later run's manifest,
    # not in the original compiler's stdout. Resolve those explicit entries too.
    for entry in list(artifacts.values()):
        if not entry["remote_path"].endswith("-manifest.json"):
            continue
        run_manifest = json.loads((RD/entry["local_path"]).read_text())
        task = entry["remote_path"].rsplit("/",1)[0]
        for item in run_manifest["files"]:
            if item["category"] != "new_checked":
                continue
            local, raw = EX/Path(item["overlay"]).name, task+"/overlay/"+item["overlay"]
            if (raw,item["sha256"]) in artifacts:
                continue
            if local.exists() and sha(local) == item["sha256"]:
                artifacts[(raw,item["sha256"])] = {"remote_path": raw, "local_path": relative(local),
                                                    "sha256": item["sha256"]}
            else:
                missing.append({"manifest": entry["local_path"], "remote_path": raw,
                                "sha256": item["sha256"]})
    return {**{key: manifest[key] for key in ("research","borrowed","mathlib","lean_commit")},
            "status": "transfer_inventory_not_final_evidence",
            "manifest": {"path": relative(initial), "sha256": sha(initial)},
            "artifacts": list(artifacts.values()), "runs": runs, "unmapped_artifacts": missing}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transfer", type=Path, default=RD/"adaptive-tail-transfer.json")
    parser.add_argument("--check-recorded", action="store_true")
    parser.add_argument("--prepare-receipt", action="store_true",
                        help="emit metadata for existing transferred bytes only; no transfer or evidence success")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded, "receipt generation is not a completed evidence check")
        receipt = receipt_inventory()
        print(json.dumps(receipt, indent=2))
        return 1 if receipt["unmapped_artifacts"] else 0
    transfer_error = None
    try:
        transfer = Transfer(args.transfer)
    except (OSError, ValueError, KeyError) as error:
        transfer, transfer_error = Transfer(None), str(error)
    out = {"schema": "aspis-v8-off-family-tail-evidence-v1", "parent_revision": BASE,
           "borrowed_formal_revision": BORROWED, "mathlib_revision": MATHLIB,
           "lean_commit": LEAN, "status": "pending", "leaves": leaves(transfer),
           "transfer_receipt_sha256": sha(args.transfer) if transfer.data else None,
           "unmapped_transferred_artifacts": transfer.data.get("unmapped_artifacts", []) if transfer.data else [],
           "transfer_error": transfer_error,
           "scope": "current-source focused ideal-game mathematics and restricted host controls; no complete V8 security certificate",
           "proof_body_bytes": 40282, "positive_work_credit": 0,
           "global_accepted_extraction_bound": None, "remaining_global_allowance": None}
    for name, check in (("exact_arithmetic", arithmetic), ("overlap_control", overlap)):
        try:
            out[name] = check()
        except (OSError, ValueError, KeyError, StopIteration) as error:
            out[name] = {"status": "pending", "reason": str(error)}
    complete = (not transfer_error and all(row["status"] == "green" for row in out["leaves"])
                and out["exact_arithmetic"]["status"] == out["overlap_control"]["status"] == "green")
    out["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "pending/missing current endpoints: refusing recorded-evidence success")
        require(json.loads((RD/"off-family-tail-evidence.json").read_text()) == out,
                "recorded evidence differs from current sources/logs/artifacts")
        print("Current adaptive-tail focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(out, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("ADAPTIVE_TAIL_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
