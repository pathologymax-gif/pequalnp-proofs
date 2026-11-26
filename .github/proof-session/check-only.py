"""Validate clean candidate branches without acquiring or handling a project lease."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import time

path = Path(__file__).with_name("promise-worker.py")
spec = importlib.util.spec_from_file_location("upstream_session", path)
w = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w)
assert os.environ["GITHUB_REPOSITORY"] == w.FORK
assert os.environ["GITHUB_ACTOR"] == w.OWNER
assert os.environ["GITHUB_REF"] == "refs/heads/promise44-validation"
slot = os.environ["PROOF_SLOT"]
assert slot in ("1", "2", "3")
manifest = ".github/proof-session/check-only-" + slot + ".json"
stop = time.monotonic() + 45 * 60
seen = set()
pinned = w.git("rev-parse", "HEAD").decode().strip()
while time.monotonic() < stop:
    w.git("fetch", "--quiet", w.FORK_URL, "refs/heads/promise44-validation")
    if not w.git("ls-tree", "FETCH_HEAD", "--", manifest):
        time.sleep(15)
        continue
    target = json.loads(w.git("show", "FETCH_HEAD:" + manifest))
    step, commit = target.get("step", ""), target.get("commit", "")
    if target.get("run") != os.environ["GITHUB_RUN_ID"] or (step,commit) in seen:
        time.sleep(15)
        continue
    assert re.fullmatch(r"L-[a-z]+-\d+", step)
    assert re.fullmatch(r"[0-9a-f]{40}",commit)
    os.environ["PNP_CHECKED_STEP"] = step
    os.environ["PNP_CHECKED_COMMIT"] = commit
    seen.add((step,commit))
    try:
        ev = w.proof_of_evidence(pinned)
    except w.StepClosed as exc:
        print("CLOSED PRIOR TO LEASING",step,str(exc),flush=True)
        continue
    except w.Stop as exc:
        print("CANDIDATE REJECTED",step,str(exc),flush=True)
        raise SystemExit(1)
    assert ev and ev["id"] == step and ev["commit"] == commit
    digest = hashlib.sha256(w.git("show",commit+":"+ev["descriptor"][1])).hexdigest()
    data = dict(step=step, commit=commit, upstream=pinned, sha256=digest, accepted=True)
    output=Path(os.environ["RUNNER_TEMP"],"checked-proof.json")
    output.write_text(json.dumps(data,indent=2),encoding="utf-8")
    print("ACCEPTED BY PINNED CHECKER",step,commit,digest,flush=True)
    break
else:
    print("Window ended without a submitted proof candidate. No lease was requested.")
