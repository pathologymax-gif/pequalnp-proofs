"""Prepare one clean fork branch for a newly opened one-a-side circuit problem.

The desk connections are read-only. A separate validator checks the exact
statement using the official checker before seeking a proof-specific lease.
"""

import base64
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

from formula_search import evaluate_on_pairs, formulas, gates_for
from generate_lean import render


FORK = "pathologymax-gif/pequalnp-proofs"
UPSTREAM = "open-goat/pequalnp-proofs"
DESK = "https://pequalnp-desk.pequalnp.workers.dev/desk/"
GITHUB = "https://api.github.com/"
ROW = re.compile(r"The 4 by 4 bipartite graph with mask (\d+) is represented on the one-a-side promise "
                 r"by an AND/OR/NOT circuit of fan-in two with at most (\d+) gates?")
FIRST_NEW = 19117
CHECK_RUN = "45786134580"
CHECK_BRANCH = "promise44-validation"
CHECK_FILE = ".github/proof-session/check-only-3.json"
CUTOFF = datetime(2026, 12, 2, 3, 22, 45, tzinfo=timezone.utc).timestamp()
PUBLIC_KEYS = ("id", "title", "held", "parallel", "cap", "level", "kind", "offerable",
               "points", "reason", "reductions", "refutation", "pr_open", "lane")


def read_json(url, query=None):
    url += ("?" + urlencode(query)) if query else ""
    headers = {"User-Agent": "Brett-Snodgrass-mathematical-research"}
    if url.startswith(GITHUB):
        headers["Authorization"] = "Bearer " + os.environ["GH_TOKEN"]
        headers["Accept"] = "application/vnd.github+json"
    with urlopen(Request(url, headers=headers), timeout=17) as res:
        return json.load(res)


def git(*args, cwd=None):
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def public_snapshot(board):
    return {"updated_at": board["updated_at"], "offerable_now": board.get("offerable_now"),
            "gaps": [{k: g[k] for k in PUBLIC_KEYS if k in g} for g in board["gaps"]]}


def save_snapshot(board, directory):
    (directory / "board_public.json").write_text(json.dumps(public_snapshot(board)), encoding="utf-8")


def candidates(board):
    found = []
    for g in board["gaps"]:
        ident = re.fullmatch(r"L-meta-(\d+)", g.get("id", ""))
        row = ROW.fullmatch(g.get("title", ""))
        if not ident or not row or g.get("kind") != "prove" or g.get("held") != 0:
            continue
        n, mask, cap = int(ident[1]), int(row[1]), int(row[2])
        if n >= FIRST_NEW and 0 <= mask < 65536 and 1 <= cap <= 12:
            found.append((n, mask, cap))
    return sorted(found, reverse=True)


def has_competitor(step):
    q = f'repo:{UPSTREAM} is:pr is:open "{step}" in:title'
    result = read_json(GITHUB + "search/issues", {"q": q, "per_page": 1})
    return result["total_count"] != 0 or result.get("incomplete_results", True)


def dispatch_check(step, commit):
    prefix = GITHUB + "repos/" + FORK
    run = read_json(f"{prefix}/actions/runs/{CHECK_RUN}")
    if run["status"] != "in_progress" or run["head_branch"] != CHECK_BRANCH:
        print("Reserved validator has ended; candidate available for independent checking.", flush=True)
        return
    url = f"{prefix}/contents/{CHECK_FILE}"
    item = {"run": CHECK_RUN, "step": step, "commit": commit}
    payload = {"branch": CHECK_BRANCH, "message": f"Check the single-file proof of {step}",
               "content": base64.b64encode((json.dumps(item) + "\n").encode()).decode()}
    try:
        prior = read_json(url, {"ref": CHECK_BRANCH})
    except HTTPError as exc:
        if exc.code != 404:
            raise
    else:
        prior_manifest = json.loads(base64.b64decode(prior["content"]))
        if prior_manifest.get("run") == CHECK_RUN:
            print("The reserved validator slot already has a manifest.", flush=True)
            return
        payload["sha"] = prior["sha"]
    request = Request(url, data=json.dumps(payload).encode(), method="PUT", headers={
        "Authorization": "Bearer " + os.environ["GH_TOKEN"], "User-Agent": "proof-scout",
        "Accept": "application/vnd.github+json", "Content-Type": "application/json"})
    with urlopen(request, timeout=17) as response:
        updated = json.load(response)
    print(f"Dispatched {step} to reserved validator slot 3 at {updated['commit']['sha']}", flush=True)


def prepare(n, mask, cap, dictionary, artifacts):
    step = f"L-meta-{n}"
    if mask not in dictionary:
        return False
    gates, out = gates_for(mask, dictionary)
    if len(gates) > cap or evaluate_on_pairs(gates, out) != mask:
        return False
    time.sleep(4)
    gap_response = read_json(DESK + "row", {"gap": step})
    rows = [r for r in gap_response["gaps"] if r.get("id") == step]
    path = f"lean/PEqualNP/Outside/L_meta_{n}.lean"
    module = f"PEqualNP.Outside.L_meta_{n}"
    if len(rows) != 1:
        return False
    gap = rows[0]
    if gap.get("file") != path or gap.get("module") != module or gap.get("pr_open") != 0:
        return False
    proof = render(n, {"mask": mask, "bound": cap, "gates": gates, "output": out})
    statement = proof.rsplit(f"theorem {module} :", 1)[1].split(":= by", 1)[0]
    if "".join(statement.split()) != "".join(gap["statement"].split()):
        print(f"{step}: family statement differs from recognized template", flush=True)
        return False
    fork_url = "https://github.com/" + FORK + ".git"
    ref = "refs/heads/" + step
    if git("ls-remote", "--heads", fork_url, ref):
        return False
    git("fetch", "--no-tags", "--depth=1", "https://github.com/" + UPSTREAM + ".git", "refs/heads/main")
    upstream = git("rev-parse", "FETCH_HEAD")
    with tempfile.TemporaryDirectory() as temp:
        git("worktree", "add", "--quiet", "--detach", temp, upstream)
        try:
            p = Path(temp, path)
            if p.exists() or Path(temp, "STOP").exists():
                return False
            p.write_bytes(proof.encode("utf-8"))
            git("add", "--", path, cwd=temp)
            if git("diff", "--cached", "--name-only", cwd=temp) != path:
                raise RuntimeError("Expected exactly the one assigned path")
            git("-c", "user.name=github-actions[bot]", "-c",
                "user.email=41898282+github-actions[bot]@users.noreply.github.com",
                "commit", "--quiet", "-m", f"Prove {step} with an explicit circuit", cwd=temp)
            sha = git("rev-parse", "HEAD", cwd=temp)
            if has_competitor(step) or read_json(DESK + "step", {"gap": step}).get("state") != "open":
                return False
            git("-c", "credential.helper=", "-c", "credential.https://github.com.helper=!gh auth git-credential",
                "push", f"--force-with-lease={ref}:", fork_url, f"HEAD:{ref}", cwd=temp)
            if git("ls-remote", "--heads", fork_url, ref).split()[0] != sha:
                raise RuntimeError("The new fork head could not be verified")
        finally:
            git("worktree", "remove", "--force", temp)
    item = {"step": step, "commit": sha, "base": upstream, "mask": mask,
            "gate_bound": cap, "gates": len(gates), "path": path}
    (artifacts / "candidate.json").write_text(json.dumps(item, indent=2))
    print("CANDIDATE", json.dumps(item), flush=True)
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as f:
        f.write(f"[Candidate {step}](https://github.com/{FORK}/commit/{sha}) with {len(gates)} gates.\n")
    try:
        dispatch_check(step, sha)
    except (TimeoutError, URLError) as exc:
        print(f"Candidate saved; validator dispatch needs review: {type(exc).__name__}", flush=True)
    return True


def main():
    if os.environ.get("GITHUB_REPOSITORY") != FORK:
        raise RuntimeError("This monitor only serves the designated fork")
    directory = Path(os.environ["RUNNER_TEMP"], "public-proof-scout")
    directory.mkdir(exist_ok=True)
    if time.time() >= CUTOFF:
        print("Weekly research window has closed.")
        return
    if sys.argv[1:] == ["snapshot"]:
        save_snapshot(read_json(DESK + "board"), directory)
        return
    if sys.argv[1:]:
        raise ValueError("Unexpected arguments")
    # This is a bounded, one-shot job. A fresh run can prepare the next row.
    stop = min(time.time() + 7200, CUTOFF)
    known = formulas(9)
    attempted = set()
    seen_competition = set()
    polls = 0
    while time.time() < stop and len(attempted) < 3:
        try:
            b = read_json(DESK + "board")
            save_snapshot(b, directory)
            polls += 1
            print(f"Board {b['updated_at']}, poll {polls}, {len(attempted)} distinct candidates attempted", flush=True)
            for n, mask, cap in candidates(b):
                if n in attempted or n in seen_competition or mask not in known or len(gates_for(mask, known)[0]) > cap:
                    continue
                step = f"L-meta-{n}"
                if has_competitor(step):
                    seen_competition.add(n)
                    continue
                time.sleep(4)
                if read_json(DESK + "step", {"gap": step}).get("state") != "open":
                    continue
                attempted.add(n)
                if prepare(n, mask, cap, known, directory):
                    return
                if len(attempted) >= 3:
                    break
        except (TimeoutError, URLError) as exc:
            print(f"Transient public service error: {type(exc).__name__}", flush=True)
        if time.time() < stop and len(attempted) < 3:
            time.sleep(min(120, max(0, stop - time.time())))
    print("Finished bounded scouting without a new eligible proof branch.", flush=True)


if __name__ == "__main__":
    main()
