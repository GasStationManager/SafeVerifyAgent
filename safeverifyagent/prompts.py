"""Prompt resolution — one renderer, shared by every driver.

This module is small and load-bearing. Prompts live in
`safeverifyagent/prompts/*.md` as data, and EVERY driver renders them
through `render()`. The moment a driver paraphrases a prompt into its own
source, the two harnesses are running different agents and every
comparison between them is measuring the paraphrase instead of the
change you meant to test. A test asserts the drivers resolve identical
text; keep it that way.

Placeholders are `{name}` where `name` is an identifier. Anything else —
a stray brace in a code fence, a set literal in an example — is left
alone, because a renderer that chokes on prose makes prompt authors
avoid prose.
"""

from __future__ import annotations

import os
import re
from typing import Any, List

PROMPT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prompts")

_PLACEHOLDER = re.compile(r"\{([A-Za-z_][A-Za-z0-9_]*)\}")


class PromptError(RuntimeError):
    pass


def available() -> List[str]:
    return sorted(f[:-3] for f in os.listdir(PROMPT_DIR) if f.endswith(".md"))


def load(name: str) -> str:
    path = os.path.join(PROMPT_DIR, f"{name}.md")
    if not os.path.exists(path):
        raise PromptError(f"no prompt {name!r}; have {available()}")
    with open(path, encoding="utf-8") as f:
        return f.read()


def placeholders(name: str) -> List[str]:
    return sorted(set(_PLACEHOLDER.findall(load(name))))


def render(name: str, **values: Any) -> str:
    """Render `name` with `values`.

    Every placeholder must be supplied. A missing one is an error rather
    than an empty string: a prompt that silently ships `context:` with
    nothing after it reads, to the agent, as "there is no context" —
    which is a different instruction from the one you wrote.
    """
    text = load(name)
    missing = sorted(set(_PLACEHOLDER.findall(text)) - set(values))
    if missing:
        raise PromptError(
            f"prompt {name!r} needs {missing}; got {sorted(values)}")
    return _PLACEHOLDER.sub(lambda m: str(values[m.group(1)]), text)
