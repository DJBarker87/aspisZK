#!/usr/bin/env python3
"""Check the emitted field-reader skeleton against the decoder-generic owner."""
import re
from pathlib import Path

packet = Path(__file__).resolve().parent
generated = (packet / "AspisR1WeightsPairCut.Funs.lean").read_text()
generic = (packet / "WeightsFieldExplicitDecoder.lean").read_text()

def extract(text: str, start: str, end: str) -> str:
    a = text.index(start)
    b = text.index(end, a)
    return text[a:b]

emitted = extract(generated, "def weights.field\n", "/-- [aspis_r1_weights_pair_cut::weights::push_byte_products")
selected = extract(generic, "def weights.field\n", "\n\nend AspisR1WeightsFieldCurrent")

# Ignore formatting and generated namespace qualification, but preserve token
# order and every operation name/argument. The one intentional difference is
# the final decoder's source name versus the decoder parameter.
emitted_body = re.sub(r"\s+", " ", emitted)
selected_body = re.sub(r"\s+", " ", selected)
emitted_body = emitted_body.replace("field.WideExact.from_le_bytes s", "decode s")
assert "let i1 ← i * 32#usize" in emitted_body
assert "let i2 ← i + 1#usize" in emitted_body
assert "let i3 ← i2 * 32#usize" in emitted_body
assert "core.slice.index.Slice.index" in emitted_body
assert "core.option.Option.unwrap o" in emitted_body
assert "field.WideExact.from_le_bytes s" not in emitted_body
assert "let o ← decode s" in emitted_body
emitted_ops = emitted_body.split(" := do ", 1)[1].strip()
selected_ops = selected_body.split(" := do ", 1)[1].strip()
assert emitted_ops == selected_ops, "operation body differs beyond decoder substitution"

# Both owners have the same checked selector steps, with the actual emitted
# operation sequence accounted for explicitly above. Check those tokens occur
# in the same ordered sequence in both generated sources.
tokens = [
    "let i1 ← i * 32#usize", "let i2 ← i + 1#usize",
    "let i3 ← i2 * 32#usize", "core.slice.index.Slice.index",
    "let o ← decode s", "core.option.Option.unwrap o",
]
for body, label in ((emitted_body, "emitted"), (selected_body, "selected")):
    pos = -1
    for token in tokens:
        nxt = body.find(token, pos + 1)
        assert nxt >= 0, f"{label} selector missing/out of order: {token}"
        pos = nxt

assert "field.WideExact.from_le_bytes" in emitted
assert "def weights.field" in generic
print("PASS: emitted body has the decoder-generic checked selector order")
