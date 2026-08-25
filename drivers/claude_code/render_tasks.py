"""Render one task block per obligation, for dispatch as subagents.

Prints the exact text a worker should receive. Nothing here paraphrases
a prompt — `safeverifyagent.prompts.render` is the only source, shared
with the API driver.
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", ".."))

from safeverifyagent import checkers, prompts                # noqa: E402
from safeverifyagent.extract import extract                  # noqa: E402
from safeverifyagent.verdict import BARE, PAIRED             # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("artifact")
    ap.add_argument("--intake", choices=(BARE, PAIRED), default=BARE)
    ap.add_argument("--rung", choices=("check", "coherence"), default="check")
    a = ap.parse_args()

    result = extract(a.artifact)
    if result.degraded:
        # Loud, because an obligation nobody extracted is an obligation
        # nobody audits, and a short list looks exactly like an easy file.
        print(f"!! DEGRADED EXTRACTION: {result.note}\n", file=sys.stderr)
    avail = json.dumps(checkers.available())

    print(f"# {len(result)} obligation(s); dispatch these in PARALLEL\n")
    for ob in result:
        common = dict(obligation_id=ob.id, statement=ob.statement,
                      context=", ".join(ob.depends_on) or "(none)",
                      artifact_path=os.path.abspath(a.artifact))
        if a.rung == "check":
            body = prompts.render("check", checkers_available=avail, **common)
        else:
            body = prompts.render(
                "coherence",
                check_summary="(supply this obligation's check-rung result)",
                **common)
        print(f"\n{'=' * 70}\n=== TASK: {a.rung} rung on {ob.id}\n{'=' * 70}\n")
        print(body)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
