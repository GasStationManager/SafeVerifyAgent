# Claude Code driver

Audit a claimed proof from a Claude Code session, with no API code and
nothing to deploy. This is the path for auditing something today; use
`drivers/audit.py` when you need a run to be reproducible.

```bash
# 1. read the obligations out of the artifact
python3 drivers/claude_code/render_tasks.py Claimed.lean --intake bare

# 2. dispatch one subagent per printed task block, in parallel
# 3. collect the JSON each returns, then aggregate:
python3 drivers/claude_code/collect.py findings.jsonl --intake bare
```

`render_tasks.py` renders the shipped prompts through
`safeverifyagent.prompts` — the same renderer `audit.py` uses. The
agent definitions in `agents/` are deliberately thin: they set the
caste's identity and say that the instructions arrive in the task
prompt. If a prompt's substance ever migrates into an agent definition,
the two drivers are running different agents and every comparison
between them measures the paraphrase instead of the change under test.
