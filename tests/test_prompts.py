"""One renderer, and no driver may paraphrase a prompt.

The rule looks like tidiness and is not. The moment a driver embeds its
own copy of a prompt, the two harnesses are running different agents, and
every comparison between them measures the paraphrase rather than the
change you meant to test. Mode parity has to be structural or it is not a
property at all.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from safeverifyagent import prompts                          # noqa: E402

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
DRIVERS = os.path.join(ROOT, "drivers")


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def driver_sources():
    for base, _dirs, files in os.walk(DRIVERS):
        for f in files:
            if f.endswith((".py", ".md")):
                yield os.path.join(base, f)


def prose_lines(text, min_words=8):
    """Distinctive sentences of a prompt: long prose lines, no markup."""
    for line in text.splitlines():
        line = line.strip()
        if (len(line.split()) >= min_words and not line.startswith(("|", "#", "-", "`", ">"))
                and "{" not in line):
            yield line


class TestRendering(unittest.TestCase):
    def test_every_prompt_is_loadable_and_lists_its_placeholders(self):
        self.assertTrue(prompts.available())
        for name in prompts.available():
            self.assertTrue(prompts.load(name).strip())

    def test_a_missing_placeholder_is_an_error_not_an_empty_string(self):
        """A prompt that ships `context:` with nothing after it reads, to
        the agent, as 'there is no context' — a different instruction
        from the one that was written."""
        with self.assertRaises(prompts.PromptError):
            prompts.render("coherence", obligation_id="h1")

    def test_render_substitutes_every_placeholder(self):
        vals = {p: f"<{p}>" for p in prompts.placeholders("check")}
        out = prompts.render("check", **vals)
        self.assertNotIn("{obligation_id}", out)
        for p in vals:
            self.assertIn(f"<{p}>", out)

    def test_an_unknown_prompt_names_the_ones_that_exist(self):
        with self.assertRaises(prompts.PromptError) as cm:
            prompts.render("nope")
        self.assertIn("coherence", str(cm.exception))

    def test_stray_braces_in_prose_do_not_break_rendering(self):
        """A renderer that chokes on a set literal makes prompt authors
        avoid prose, which is the opposite of what we want."""
        import safeverifyagent.prompts as P
        self.assertEqual(P._PLACEHOLDER.findall("use {1, 2} and {name}"),
                         ["name"])


class TestNoDriverParaphrasesAPrompt(unittest.TestCase):
    def test_no_driver_embeds_prompt_prose(self):
        offenders = []
        sources = {p: read(p) for p in driver_sources()}
        for name in prompts.available():
            for line in prose_lines(prompts.load(name)):
                for path, src in sources.items():
                    if line in src:
                        offenders.append(
                            f"{os.path.relpath(path, ROOT)} copies "
                            f"{name}.md: {line[:60]}...")
        self.assertEqual(offenders, [], "\n".join(offenders))

    def test_every_driver_that_prompts_a_model_uses_the_renderer(self):
        """A driver that builds its own message body has, by definition,
        stopped sharing the prompts."""
        for path in driver_sources():
            if not path.endswith(".py"):
                continue
            src = read(path)
            if "system=" in src or "TASK" in src:
                self.assertIn("prompts.render", src,
                              f"{os.path.relpath(path, ROOT)} prompts a "
                              "model without going through the renderer")


if __name__ == "__main__":
    unittest.main()
