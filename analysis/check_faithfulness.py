#!/usr/bin/env python3
"""
Faithfulness checks for the wani Search Log visualisation tool.

Reads a /searchlog/events JSON dump and verifies three structural
invariants that the Search Tree reconstruction depends on:

  (1) Goal pairing:       every EvGoalStart has exactly one matching EvGoalEnd
  (2) Outcome uniqueness: each goal has at most one terminal outcome event
  (3) Depth invariant:    every EvGoalStart at depth d (>1) has an active
                          parent at depth d-1 in the live recursion stack

Usage:
    python3 check_faithfulness.py <events.json>
"""

import json
import sys
from collections import defaultdict

OUTCOME_KINDS = {
    "deduced", "deduce_failed", "depth_exceeded",
    "avoid_loop", "time_limit", "special_case",
}


def check_goal_pairing(events):
    """Every EvGoalStart has exactly one matching EvGoalEnd, and vice versa."""
    starts = [e for e in events if e["kind"] == "goal_start"]
    ends = [e for e in events if e["kind"] == "goal_end"]
    start_ids = [e["goalId"] for e in starts]
    end_ids = [e["goalId"] for e in ends]

    duplicate_starts = len(start_ids) - len(set(start_ids))
    duplicate_ends = len(end_ids) - len(set(end_ids))

    start_set = set(start_ids)
    end_set = set(end_ids)
    missing_end = start_set - end_set
    extra_end = end_set - start_set

    ok = (
        len(starts) == len(ends)
        and duplicate_starts == 0
        and duplicate_ends == 0
        and not missing_end
        and not extra_end
    )
    return {
        "name": "goal pairing",
        "pass": ok,
        "starts": len(starts),
        "ends": len(ends),
        "duplicate_starts": duplicate_starts,
        "duplicate_ends": duplicate_ends,
        "missing_end": len(missing_end),
        "extra_end": len(extra_end),
    }


def check_outcome_uniqueness(events):
    """Each goalId carries at most one terminal outcome event."""
    counts = defaultdict(int)
    for e in events:
        if e["kind"] in OUTCOME_KINDS:
            counts[e["goalId"]] += 1
    duplicated = {gid: c for gid, c in counts.items() if c > 1}
    return {
        "name": "outcome uniqueness",
        "pass": not duplicated,
        "goals_with_outcome": len(counts),
        "goals_with_duplicate_outcome": len(duplicated),
        "max_outcomes_per_goal": max(counts.values(), default=0),
    }


def check_depth_invariant(events):
    """Every goal_start at depth d>1 has an active predecessor at depth d-1.

    "Active" means: a goal_start at depth d-1 that occurred before and whose
    goal_end has not yet been emitted. This formalises the strict depth-first
    recursion contract that buildSearchTree's depth-based parent inference
    relies on.
    """
    # Walk events in id order. Maintain stack of active goal_starts by depth.
    active_at_depth = {}  # depth -> goalId of currently active goal at that depth
    violations = []
    starts_seen = 0
    starts_at_root = 0  # depth 1 (no parent expected by buildParentMap)

    for e in sorted(events, key=lambda x: x["id"]):
        if e["kind"] == "goal_start":
            starts_seen += 1
            d = e["depth"]
            if d == 1:
                starts_at_root += 1
            else:
                # require an active predecessor at depth d-1
                if (d - 1) not in active_at_depth:
                    violations.append({
                        "id": e["id"],
                        "depth": d,
                        "reason": f"no active goal at depth {d - 1}",
                    })
            active_at_depth[d] = e["goalId"]
        elif e["kind"] == "goal_end":
            d = e["depth"]
            if active_at_depth.get(d) == e["goalId"]:
                del active_at_depth[d]
            # If the active goal at this depth is something else, we don't
            # treat that as a violation here; the goal_pairing check covers it.

    return {
        "name": "depth invariant",
        "pass": not violations,
        "total_goal_starts": starts_seen,
        "starts_at_root_depth": starts_at_root,
        "violations": len(violations),
        "first_violations": violations[:5],
    }


def main():
    if len(sys.argv) != 2:
        print(__doc__.strip())
        sys.exit(1)

    path = sys.argv[1]
    with open(path) as f:
        data = json.load(f)
    events = data["events"]

    print(f"=== Faithfulness checks: {path} ===")
    print(f"total events: {len(events)}")
    print()

    checks = [
        check_goal_pairing(events),
        check_outcome_uniqueness(events),
        check_depth_invariant(events),
    ]

    n_pass = 0
    for c in checks:
        status = "PASS" if c["pass"] else "FAIL"
        print(f"[{status}] {c['name']}")
        for k, v in c.items():
            if k in ("name", "pass"):
                continue
            print(f"    {k}: {v}")
        print()
        if c["pass"]:
            n_pass += 1

    print(f"summary: {n_pass}/{len(checks)} checks passed")
    sys.exit(0 if n_pass == len(checks) else 1)


if __name__ == "__main__":
    main()
