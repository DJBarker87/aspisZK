"""Arithmetic upper-envelope calculator, never a calibrated CU theorem."""
from dataclasses import dataclass
from typing import Iterable

@dataclass(frozen=True)
class Component:
    name: str
    maximum_count: int | None
    maximum_unit_cu: int | None
    count_theorem: str | None
    calibration_hash: str | None


def envelope(fixed_cu: int, components: Iterable[Component], limit: int) -> dict:
    if fixed_cu < 0 or limit < 0:
        raise ValueError('negative CU')
    missing = []; total = fixed_cu
    for c in components:
        if c.maximum_count is None or c.maximum_unit_cu is None or not c.count_theorem or not c.calibration_hash:
            missing.append(c.name)
            continue
        if min(c.maximum_count, c.maximum_unit_cu) < 0:
            raise ValueError('negative count/cost')
        total += c.maximum_count*c.maximum_unit_cu
    return {'status': 'BLOCKED' if missing else ('NUMERIC_PASS' if total < limit else 'NUMERIC_FAIL'),
            'known_cu': total, 'headroom': limit-total, 'missing': missing,
            'scope': 'supplied arithmetic envelope; not evidence of source count/cost validity'}
