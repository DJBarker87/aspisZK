#!/usr/bin/env python3
"""Offline, source-pinned Poseidon empty-root recurrence data generator.

This is a data generator, not a Lean proof or refinement argument. It parses
all literal arrays from the selected Lean and Rust source files, requires exact
literal equality for every table, evaluates the fixed M31 Poseidon2 relation,
and can check the committed row-zero Lean/JSON outputs without modifying them.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
LEAN_ROOT = ROOT / "docs/research/v8-r0-sem-proof-20261008/lean/R0P"
RUST = ROOT / "crates/aspis-statement/src/poseidon2.rs"
EMPTY_RUST = ROOT / "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal_constants.rs"
FIELD_RUST = ROOT / "crates/aspis-core/src/field.rs"
FORMAT_RUST = ROOT / "crates/aspis-statement/src/pool_v1/format.rs"
LEAN_OUT_DIR = ROOT / "docs/research/100bit-spend-path-20261013/lean"
EVIDENCE_OUT_DIR = ROOT / "docs/research/100bit-spend-path-20261013/evidence/empty-root-preflight-20261013"
OUT_LEAN = LEAN_OUT_DIR / "EmptyRootZeroData.lean"
OUT_JSON = EVIDENCE_OUT_DIR / "empty-root-data.json"
NODE_TWEAK = 1051521018


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_ints(text: str) -> list[int]:
    tokens = re.findall(r"0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*|(?<![\w])\d(?:_?\d)*", text)
    return [int(token.replace("_", ""), 0 if token.lower().startswith("0x") else 10) for token in tokens]


def lean_rhs(name: str, file: Path) -> str:
    text = file.read_text()
    match = re.search(rf"\bdef\s+{re.escape(name)}\b[^\n]*:=", text)
    if not match:
        raise ValueError(f"Lean definition {name} not found in {file}")
    rhs = text[match.end():]
    stop = re.search(r"\n\n(?:/--|attribute\b|end\b)", rhs)
    return rhs[:stop.start()] if stop else rhs


def rust_const_rhs(name: str, file: Path) -> str:
    text = file.read_text()
    match = re.search(rf"\bconst\s+{re.escape(name)}\b[^=]*=", text)
    if not match:
        raise ValueError(f"Rust constant {name} not found in {file}")
    rhs = text[match.end():]
    stop = re.search(r"\];", rhs)
    if stop:
        return rhs[:stop.start()]
    stop = re.search(r";", rhs)
    if not stop:
        raise ValueError(f"Rust constant {name} has no terminator in {file}")
    return rhs[:stop.start()]


def chunks(values: list[int], width: int) -> list[list[int]]:
    if len(values) % width:
        raise ValueError(f"literal count {len(values)} is not a multiple of {width}")
    return [values[i:i + width] for i in range(0, len(values), width)]


def parse_sources() -> dict:
    poseidon_lean = LEAN_ROOT / "PoseidonConstants.lean"
    empty_lean = LEAN_ROOT / "EmptyRoots.lean"
    sources = [poseidon_lean, empty_lean, LEAN_ROOT / "Poseidon.lean",
               LEAN_ROOT / "Semantics.lean", RUST, EMPTY_RUST, FIELD_RUST, FORMAT_RUST]
    for path in sources:
        if not path.is_file():
            raise FileNotFoundError(path)

    lean_initial = parse_ints(lean_rhs("poseidonExternalInitial", poseidon_lean))
    lean_final = parse_ints(lean_rhs("poseidonExternalFinal", poseidon_lean))
    lean_internal = parse_ints(lean_rhs("poseidonInternalConstants", poseidon_lean))
    lean_shifts = parse_ints(lean_rhs("poseidonInternalShifts", poseidon_lean))
    lean_roots = parse_ints(lean_rhs("emptyRootsNat", empty_lean))
    rust_initial = parse_ints(rust_const_rhs("EXTERNAL_INITIAL", RUST))
    rust_final = parse_ints(rust_const_rhs("EXTERNAL_FINAL", RUST))
    rust_internal = parse_ints(rust_const_rhs("INTERNAL", RUST))
    rust_shifts = parse_ints(rust_const_rhs("INTERNAL_SHIFTS", RUST))
    rust_roots = parse_ints(rust_const_rhs("POOL_V1_PAIR_EMPTY_ROOTS_V1", EMPTY_RUST))

    literal_pairs = {
        "poseidonExternalInitial": (lean_initial, rust_initial),
        "poseidonExternalFinal": (lean_final, rust_final),
        "poseidonInternalConstants": (lean_internal, rust_internal),
        "poseidonInternalShifts": (lean_shifts, rust_shifts),
        "emptyRootsNat": (lean_roots, rust_roots),
    }
    for name, (lean_values, rust_values) in literal_pairs.items():
        if lean_values != rust_values:
            raise ValueError(f"Lean/Rust literal mismatch for {name}")

    p_match = re.search(r"\bpub\s+const\s+P\s*:\s*u32\s*=\s*(0x[0-9a-fA-F_]+|\d[\d_]*)", FIELD_RUST.read_text())
    tweak_match = re.search(r"\bMERKLE_NODE_COMPRESSION_V3_TWEAK\s*:\s*M31\s*=\s*M31\((0x[0-9a-fA-F_]+|\d[\d_]*)\)", RUST.read_text())
    if not p_match or not tweak_match:
        raise ValueError("Could not parse M31 modulus or Rust Merkle node tweak")
    modulus = int(p_match.group(1).replace("_", ""), 0)
    rust_tweak = int(tweak_match.group(1).replace("_", ""), 0)
    if modulus != 2**31 - 1:
        raise ValueError(f"unexpected M31 modulus {modulus}")
    if (-NODE_TWEAK) % modulus != rust_tweak % modulus:
        raise ValueError("lane-15 subtractive offset does not equal Rust node tweak modulo P")

    initial = chunks(lean_initial, 16)
    final = chunks(lean_final, 16)
    roots = chunks(lean_roots, 8)
    if len(initial) != 4 or len(final) != 4 or len(lean_internal) != 14 or len(lean_shifts) != 15:
        raise ValueError("unexpected Poseidon2 round schedule dimensions")
    if len(roots) != 21:
        raise ValueError(f"expected 21 frozen empty-root rows, found {len(roots)}")
    if any(not 0 <= value < modulus for row in initial + final for value in row):
        raise ValueError("noncanonical external round constant")
    if any(not 0 <= value < modulus for value in lean_internal):
        raise ValueError("noncanonical internal round constant")
    if any(not 0 <= value < modulus for row in roots for value in row):
        raise ValueError("noncanonical frozen empty-root table entry")

    return {
        "modulus": modulus,
        "rust_tweak": rust_tweak,
        "external_initial": initial,
        "external_final": final,
        "internal_constants": lean_internal,
        "internal_shifts": lean_shifts,
        "frozen_roots": roots,
        "source_hashes": {str(path.relative_to(ROOT)): sha256(path) for path in sources},
    }


def add(a: int, b: int, p: int) -> int:
    return (a + b) % p


def sub(a: int, b: int, p: int) -> int:
    return (a - b) % p


def mul(a: int, b: int, p: int) -> int:
    return (a * b) % p


def pow5(a: int, p: int) -> int:
    square = mul(a, a, p)
    return mul(mul(square, square, p), a, p)


def mat4(values: list[int], p: int) -> list[int]:
    a, b, c, d = values
    t01 = add(a, b, p)
    t23 = add(c, d, p)
    t0123 = add(t01, t23, p)
    t01123 = add(t0123, b, p)
    t01233 = add(t0123, d, p)
    out3 = add(t01233, add(a, a, p), p)
    out1 = add(t01123, add(c, c, p), p)
    out0 = add(t01123, t01, p)
    out2 = add(t01233, t23, p)
    return [out0, out1, out2, out3]


def external_linear(state: list[int], p: int) -> list[int]:
    out = []
    for start in range(0, 16, 4):
        out.extend(mat4(state[start:start + 4], p))
    sums = [0, 0, 0, 0]
    for column in range(4):
        for row in range(4):
            sums[column] = add(sums[column], out[row * 4 + column], p)
    return [add(value, sums[index & 3], p) for index, value in enumerate(out)]


def internal_linear(state: list[int], shifts: list[int], p: int) -> list[int]:
    part_sum = 0
    for value in state[1:]:
        part_sum = add(part_sum, value, p)
    full_sum = add(part_sum, state[0], p)
    out = [sub(part_sum, state[0], p)]
    for index in range(1, 16):
        diagonal = 1 << shifts[index - 1]
        out.append(add(full_sum, mul(state[index], diagonal, p), p))
    return out


def poseidon_trace(input_state: list[int], constants: dict) -> list[list[int]]:
    p = constants["modulus"]
    state = input_state[:]
    states = [state[:]]  # raw node input
    state = external_linear(state, p)
    states.append(state[:])  # leading external layer
    for row in constants["external_initial"]:
        state = [pow5(add(value, constant, p), p) for value, constant in zip(state, row)]
        state = external_linear(state, p)
        states.append(state[:])
    for constant in constants["internal_constants"]:
        state = state[:]
        state[0] = pow5(add(state[0], constant, p), p)
        state = internal_linear(state, constants["internal_shifts"], p)
        states.append(state[:])
    for row in constants["external_final"]:
        state = [pow5(add(value, constant, p), p) for value, constant in zip(state, row)]
        state = external_linear(state, p)
        states.append(state[:])
    if len(states) != 24:
        raise AssertionError(f"expected 24 states, got {len(states)}")
    return states


def compute(constants: dict) -> dict:
    p = constants["modulus"]
    previous = [0] * 8
    nodes = []
    for level, expected in enumerate(constants["frozen_roots"]):
        left = [0] * 8 if level == 0 else previous[:]
        right = [0] * 8 if level == 0 else previous[:]
        raw = left + right
        raw[15] = sub(raw[15], NODE_TWEAK, p)
        states = poseidon_trace(raw, constants)
        output = states[-1][:8]
        if output != expected:
            mismatch = next(i for i, (actual, frozen) in enumerate(zip(output, expected)) if actual != frozen)
            raise ValueError(f"empty-root row {level} lane {mismatch} mismatch: generated={output[mismatch]} frozen={expected[mismatch]}")
        if any(not 0 <= x < p for state in states for x in state):
            raise AssertionError("noncanonical state value")
        nodes.append({
            "level": level,
            "left": left,
            "right": right,
            "input": raw,
            "states": states,
            "output": output,
            "matches_frozen_root": True,
        })
        previous = output
    return {"nodes": nodes, "row_zero_states": nodes[0]["states"], "computed_roots": [node["output"] for node in nodes]}


def lean_data_text(constants: dict, states: list[list[int]], module_suffix: str) -> str:
    if module_suffix == "ZeroData":
        comment = "Generated literal row-zero Poseidon2 transition states. This file is data only;"
        detail = "the Python generator checks source tables and recurrences; no theorem is asserted."
        namespace_suffix = "ZeroData"
    else:
        comment = f"Generated literal row-{module_suffix} Poseidon2 transition states. This file is data only;"
        detail = "each round state is an independent literal vector; no multi-round evaluation is embedded."
        namespace_suffix = f"{module_suffix}Data"
    lines = [
        "import R0P.Semantics",
        "import AspisFormal.CircleGroupOrder",
        "",
        f"/-! {comment} -/",
        f"/-! {detail} -/",
        "/- Source SHA-256 manifest:",
    ]
    for path, digest in sorted(constants["source_hashes"].items()):
        lines.append(f"  {digest}  {path}")
    namespace = f"AspisR1.EmptyRoot{namespace_suffix}"
    lines += ["-/", "", f"namespace {namespace}", "", "open AspisCircleGroupOrder", ""]
    for i, state in enumerate(states):
        values = ", ".join(str(value) for value in state)
        lines += [f"def s{i} : Fin 16 → ZMod P :=", f"  ![{values}]", ""]
    lines += [f"end {namespace}", ""]
    return "\n".join(lines)


def lean_check_text(level: int) -> str:
    suffix = f"{level:02d}"
    lines = [
        f"import R1EmptyRoot{suffix}Data",
        "import R1PoseidonChain",
        "import R1AppendNode",
        "",
        "/-! A literal empty-root row checked as a chain of independent one-round transitions. -/",
        "/-! The generator keeps each transition as a small `decide`; it emits no full-chain `decide`. -/",
        "set_option autoImplicit false",
        f"namespace AspisR1.EmptyRoot{suffix}Check",
        f"open R0P AspisCircleGroupOrder AspisR1.EmptyRoot{suffix}Data",
        "",
        "def trajectory : Fin 24 → (Fin 16 → ZMod P) :=",
        "  ![" + ", ".join(f"s{i}" for i in range(24)) + "]",
        "",
        "theorem leading : s1 = poseidonExternalLinear s0 := by decide",
        "",
    ]
    for i in range(4):
        lines += [
            f"theorem initial_{i} : s{2+i} = poseidonFullRound s{1+i} (poseidonExternalInitial {i}) := by decide",
            "",
        ]
    for i in range(14):
        lines += [
            f"theorem internal_{i} : s{6+i} = poseidonInternalRound s{5+i} (poseidonInternalConstants {i}) := by decide",
            "",
        ]
    for i in range(4):
        lines += [
            f"theorem final_{i} : s{20+i} = poseidonFullRound s{19+i} (poseidonExternalFinal {i}) := by decide",
            "",
        ]
    lines += [
        "theorem permutation : poseidonPermutation s0 = s23 := by",
        "  apply poseidon_chain trajectory",
        "  · exact leading",
        "  · intro r",
        "    fin_cases r",
    ]
    for i in range(4):
        lines.append(f"    · exact initial_{i}")
    lines += ["  · intro r", "    fin_cases r"]
    for i in range(14):
        lines.append(f"    · exact internal_{i}")
    lines += ["  · intro r", "    fin_cases r"]
    for i in range(4):
        lines.append(f"    · exact final_{i}")
    previous = level - 1
    lines += [
        "",
        "theorem node_base :",
        f"    AppendNode.frozenEmpty (K := ZMod P) {level} =",
        f"      nodeCompress (AppendNode.frozenEmpty (K := ZMod P) {previous})",
        f"        (AppendNode.frozenEmpty (K := ZMod P) {previous}) := by",
        "  have hinput : (fun l : Fin 16 =>",
        f"    if h : l.val < 8 then AppendNode.frozenEmpty (K := ZMod P) {previous} ⟨l.val, h⟩",
        "    else if l.val = 15 then",
        f"      AppendNode.frozenEmpty (K := ZMod P) {previous} 7 - (1051521018 : ZMod P)",
        f"    else AppendNode.frozenEmpty (K := ZMod P) {previous} ⟨l.val - 8, by omega⟩) = s0 := by",
        "    unfold AppendNode.frozenEmpty emptyRootsNat",
        "    decide",
        "  have hout : digestOf s23 = AppendNode.frozenEmpty (K := ZMod P) " + str(level) + " := by",
        "    unfold AppendNode.frozenEmpty emptyRootsNat",
        "    decide",
        "  unfold nodeCompress",
        "  rw [hinput, permutation]",
        "  exact hout.symm",
        "",
        "#print axioms permutation",
        "#print axioms node_base",
        f"end AspisR1.EmptyRoot{suffix}Check",
        "",
    ]
    return "\n".join(lines)


def json_text(constants: dict, result: dict) -> str:
    data_modules = [str((LEAN_OUT_DIR / ("EmptyRootZeroData.lean" if level == 0 else f"EmptyRoot{level:02d}Data.lean")).relative_to(ROOT)) for level in range(21)]
    check_modules = [str((LEAN_OUT_DIR / f"EmptyRoot{level:02d}Check.lean").relative_to(ROOT)) for level in range(1, 21)]
    value = {
        "format": "aspis-empty-root-poseidon2-traces-v2",
        "modulus": constants["modulus"],
        "node_lane15_subtract_modulus": NODE_TWEAK,
        "rust_tweak": constants["rust_tweak"],
        "round_schedule": {"leading_external": 1, "external_initial": 4, "internal": 14, "external_final": 4},
        "source_hashes": constants["source_hashes"],
        "frozen_roots": constants["frozen_roots"],
        "computed_roots": result["computed_roots"],
        "nodes": result["nodes"],
        "lean_data_modules": data_modules,
        "lean_row_checks": check_modules,
        "round_state_split": "Each node's 24 states are independent literal definitions s0..s23; generated checkers prove leading and each of the 22 Poseidon rounds separately, then compose with poseidon_chain.",
    }
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="verify outputs without editing them")
    args = parser.parse_args()
    constants = parse_sources()
    result = compute(constants)
    generated = {OUT_LEAN: lean_data_text(constants, result["row_zero_states"], "ZeroData"),
                 OUT_JSON: json_text(constants, result)}
    for level in range(1, 21):
        suffix = f"{level:02d}"
        generated[LEAN_OUT_DIR / f"EmptyRoot{suffix}Data.lean"] = lean_data_text(
            constants, result["nodes"][level]["states"], suffix)
        generated[LEAN_OUT_DIR / f"EmptyRoot{suffix}Check.lean"] = lean_check_text(level)
    if args.check:
        bad = []
        for path, content in generated.items():
            if not path.is_file() or path.read_text() != content:
                bad.append(str(path.relative_to(ROOT)))
        if bad:
            print("generated output mismatch: " + ", ".join(bad), file=sys.stderr)
            return 1
        print(f"--check OK: {len(result['nodes'])} recursive rows; {len(generated)} generated files")
        print("all Lean/Rust literal tables match; every root matches its frozen row; every generated round state is split into an independent literal")
        return 0
    OUT_LEAN.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    for path, content in generated.items():
        path.write_text(content)
    print(f"wrote {len(generated)} generated files under the Lean and evidence directories")
    print(f"validated {len(result['nodes'])} recursive roots and emitted {len(result['nodes'])} independent 24-state trajectories")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
