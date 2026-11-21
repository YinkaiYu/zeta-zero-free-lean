"""Check the archived submissions, token counts and full patches. Requires Python 3 and Git."""
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BOARD_LEXER = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|[0-9]+|:=|=>|->|<-|[^\s]")


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def board_count(raw):
    """Replay the board count for these files, which use non-nested comments."""
    text = raw.decode("utf-8")
    text = re.sub(r"/-.*?-/|--[^\n]*", "", text, flags=re.S)
    text = re.sub(r"(?m)^\s*import\s+[^\n]+", "", text)
    return len(BOARD_LEXER.findall(text))


def main():
    results = json.loads((ROOT / "records/results.json").read_text(encoding="utf-8"))
    records = results["records"]
    with tempfile.TemporaryDirectory() as scratch:
        scratch = Path(scratch)
        subprocess.run(["git", "init", "--quiet", str(scratch)], check=True)
        work = scratch / "Solution.lean"
        previous = None
        for row in records:
            attempt = row["attempt"]
            raw = (ROOT / "snapshots" / str(attempt) / "Solution.lean").read_bytes()
            require(hashlib.sha256(raw).hexdigest() == row["source_sha256"], f"SHA-256: {attempt}")
            require(board_count(raw) == row["board_tokens"], f"Token count: {attempt}")
            leader = row["previous_pillar_leader"]["board_tokens"]
            require((row["board_tokens"] < leader) == row["pillar_record"], f"Record flag: {attempt}")
            if previous is None:
                work.write_bytes(raw)
            else:
                patch = ROOT / "diffs" / f"{previous}-to-{attempt}.diff"
                subprocess.run(["git", "-C", str(scratch), "apply", "--whitespace=nowarn",
                                str(patch)], check=True)
                require(work.read_bytes() == raw, f"Patched source: {attempt}")
            print(f"#{attempt}: {row['board_tokens']} tokens, SHA-256 verified")
            previous = attempt
        require(work.read_bytes() == (ROOT / "Solution.lean").read_bytes(), "Final source mismatch")
    print("All four patches reproduced the submitted bytes.")


if __name__ == "__main__":
    main()
