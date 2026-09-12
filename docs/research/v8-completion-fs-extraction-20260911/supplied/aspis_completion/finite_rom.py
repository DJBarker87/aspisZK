"""Exact finite-ROM experiment interpreter (tiny alphabets only).

Enumerates fresh answers uniformly. Repeated inputs reuse cached answers.
A bad-answer target is evaluated from the PRE-answer history. This is a
reference semantics and regression suite, not the actual Fiat--Shamir lift.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Hashable, Mapping

@dataclass(frozen=True)
class Step:
    message: Hashable
    answer: int
    fresh: bool
    bad: bool

History = tuple[Step, ...]
Policy = Callable[[History], Hashable | None]
Target = Callable[[History, Hashable], frozenset[int]]

@dataclass(frozen=True)
class Result:
    distribution: dict[History, Fraction]
    bad_mass: Fraction
    expected_fresh: Fraction
    worst_local_bad_fraction: Fraction


def enumerate_rom(alphabet: int, fuel: int, policy: Policy, target: Target,
                  *, max_states: int = 500000) -> Result:
    if alphabet < 1 or fuel < 0:
        raise ValueError('invalid alphabet/fuel')
    active: dict[History, Fraction] = {(): Fraction(1)}
    completed: dict[History, Fraction] = defaultdict(Fraction)
    local_max = Fraction(0)
    for _ in range(fuel):
        nxt: dict[History, Fraction] = defaultdict(Fraction)
        for history, mass in active.items():
            message = policy(history)
            if message is None:
                completed[history] += mass
                continue
            table = {step.message: step.answer for step in history}
            bad = target(history, message)
            if any(not 0 <= a < alphabet for a in bad):
                raise ValueError('bad set outside answer alphabet')
            if message in table:
                # No new independent draw and no new fresh-target trial.
                nxt[history + (Step(message, table[message], False, False),)] += mass
            else:
                local_max = max(local_max, Fraction(len(bad), alphabet))
                for answer in range(alphabet):
                    nxt[history + (Step(message, answer, True, answer in bad),)] += mass / alphabet
        if len(nxt) + len(completed) > max_states:
            raise RuntimeError('exact enumeration state cap exceeded')
        active = nxt
    for history, mass in active.items():
        completed[history] += mass
    if sum(completed.values(), Fraction(0)) != 1:
        raise AssertionError('mass was dropped')
    return Result(dict(completed),
                  sum((mass for h, mass in completed.items() if any(s.bad for s in h)), Fraction(0)),
                  sum((mass * sum(s.fresh for s in h) for h, mass in completed.items()), Fraction(0)),
                  local_max)


def grinding_success(alphabet: int, trials: int) -> Fraction:
    if alphabet < 1 or trials < 0:
        raise ValueError('invalid experiment')
    return 1 - Fraction(alphabet - 1, alphabet) ** trials
