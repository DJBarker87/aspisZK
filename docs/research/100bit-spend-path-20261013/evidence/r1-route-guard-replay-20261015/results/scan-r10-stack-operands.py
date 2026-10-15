#!/usr/bin/env python3
"""Count SBF instructions and static r10-relative stack operands in llvm-objdump text."""
import json
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
instruction_count = 0
operands = []
for line in text.splitlines():
    if re.match(r"\s*[0-9a-f]+:", line):
        instruction_count += 1
    match = re.search(r"r10 - (0x[0-9a-fA-F]+)", line)
    if match:
        operands.append((int(match.group(1), 16), line.split(':', 1)[-1].strip()))

largest = max(operands, key=lambda item: item[0], default=(0, ""))
print(json.dumps({
    "instruction_count": instruction_count,
    "r10_relative_operand_count": len(operands),
    "largest_negative_r10_offset_bytes": largest[0],
    "operands_over_4096_bytes": sum(offset > 4096 for offset, _ in operands),
    "largest_operand": largest[1],
}, indent=2))
