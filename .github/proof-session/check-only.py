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
    if (target.get("run") != os.environ.get("PROOF_QUEUE_RUN",os.environ["GITHUB_RUN_ID"])
            or step=="L-meta-19137" or (step,commit) in seen):
        time.sleep(15)
        continue
    assert re.fullmatch(r"L-[a-z]+-\d+", step)
    assert re.fullmatch(r"[0-9a-f]{40}",commit)
    os.environ["PNP_CHECKED_STEP"] = step
    os.environ["PNP_CHECKED_COMMIT"] = commit
    seen.add((step,commit))
    # Eligibility is enforced by the owner's official next/beat/submit path.
    # This service only checks mathematics, using the version on the exact clean branch.
    status, board = w.request(w.DESK + "row", {"gap":step})
    if status != 200 or not isinstance(board,dict):
        raise SystemExit("The official public row could not be read. No lease was requested.")
    found=[g for g in board.get("gaps",[]) if isinstance(g,dict) and g.get("id")==step]
    if not found and (step in (board.get("withdrawn") or {}) or
                      any(g.get("id")==step for g in board.get("checked",[]) if isinstance(g,dict))):
        print("Already settled by the project",step,flush=True)
        continue
    assert len(found)==1
    gap=found[0]
    w.guard_statement(gap)
    checked_id, proof_path = w.describe(gap)
    assert checked_id == step
    w.git("fetch", "--quiet", w.FORK_URL, "refs/heads/" + step)
    assert w.git("rev-parse","FETCH_HEAD").decode().strip() == commit
    assert w.git("diff-tree","--no-commit-id","--name-status","-r",commit) == f"A\t{proof_path}\n".encode()
    mode = w.git("ls-tree",commit,"--",proof_path).split()
    assert len(mode)==4 and mode[:2]==[b"100644",b"blob"]
    proof=w.git("cat-file","blob",mode[2].decode())
    assert 0 < len(proof) <= w.LIMIT
    if Path("STOP").exists():
        raise SystemExit("Upstream has posted STOP.")
    import tempfile
    with tempfile.TemporaryDirectory(dir=os.environ["RUNNER_TEMP"]) as directory:
        assert w.guarded_candidate(proof,proof_path,gap,directory)
        statement=Path(directory,"statement.txt")
        statement.write_text(gap["statement"],encoding="utf-8")
        filename=Path(proof_path)
        prior=filename.read_bytes() if filename.exists() else None
        try:
            filename.write_bytes(proof)
            accepted=w.check_command(["node","tools/check-lean.mjs",proof_path,str(statement),"check"],
                                     ".",time.monotonic()+46*60,lambda: None,expect_accept=True)
            if not accepted:
                raise SystemExit("The official offline checker rejected the candidate.")
            assert filename.read_bytes()==proof
        finally:
            if prior is None:filename.unlink(missing_ok=True)
            else:filename.write_bytes(prior)
    digest=hashlib.sha256(proof).hexdigest()
    data = dict(step=step, commit=commit, upstream=pinned, sha256=digest, accepted=True)
    output=Path(os.environ["RUNNER_TEMP"],"checked-proof.json")
    output.write_text(json.dumps(data,indent=2),encoding="utf-8")
    print("ACCEPTED BY PINNED CHECKER",step,commit,digest,flush=True)
    break
else:
    print("Window ended without a submitted proof candidate. No lease was requested.")
