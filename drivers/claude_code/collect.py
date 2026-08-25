"""Aggregate worker findings (one JSON object per line) into a verdict."""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", ".."))

from safeverifyagent import checkers                         # noqa: E402
from safeverifyagent.aggregate import aggregate              # noqa: E402
from safeverifyagent.extract import extract_obligations      # noqa: E402
from safeverifyagent.verdict import BARE, PAIRED, Finding    # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("findings", help="JSONL, one finding per line")
    ap.add_argument("--artifact", required=True)
    ap.add_argument("--intake", choices=(BARE, PAIRED), default=BARE)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    findings = []
    with open(a.findings, encoding="utf-8") as f:
        for line in f:
            if line.strip():
                d = json.loads(line)
                d.setdefault("intake", a.intake)
                findings.append(Finding(**d))

    v = aggregate(extract_obligations(a.artifact), findings, intake=a.intake,
                  checkers_available=checkers.available())
    print(json.dumps(v.to_dict(), indent=1) if a.json else v.headline())
    for r in v.residue:
        print(f"  residue: {r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
