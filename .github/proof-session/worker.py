"""One bounded proof-building session. Run from the upstream checkout on Linux."""

import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import sys
from time import monotonic, sleep, time
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import build_opener, HTTPRedirectHandler, Request


OWNER = "pathologymax-gif"
FORK = OWNER + "/pequalnp-proofs"
UPSTREAM = "open-goat/pequalnp-proofs"
FORK_URL = "https://github.com/" + FORK + ".git"
DESK = "https://pequalnp.com/desk/"
MODULE = re.compile(r"(?:Mathlib|PEqualNP)(?:\.[A-Za-z][A-Za-z0-9_]*)*")
LIMIT = 524288
CUTOFF = datetime(2026, 12, 2, 3, 22, 45, tzinfo=timezone.utc).timestamp()
ARTIFACT_ASSIGN = "proof-session-assignment.json"
ARTIFACT_READY = "proof-session-ready.json"


def temp_file(name):
    return Path(os.environ["RUNNER_TEMP"]) / name


def timestamp():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


class Stop(Exception):
    """Controlled message with no private data."""


class LeaseLost(Stop):
    pass


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def request(url, params, method="GET"):
    endpoint = url + "?" + urlencode(params)
    req = Request(endpoint, method=method, headers={"User-Agent": "Brett-Snodgrass-proof-session"})
    try:
        with build_opener(NoRedirect()).open(req, timeout=15) as response:
            payload = response.read(2 * 1024 * 1024 + 1)
            if len(payload) > 2 * 1024 * 1024:
                raise Stop("Remote response exceeded the size limit.")
            return response.status, json.loads(payload)
    except HTTPError as exc:
        return exc.code, None
    except (URLError, OSError, ValueError):
        raise Stop("Remote response could not be confirmed.") from None


def run(args, **kwargs):
    try:
        return subprocess.run(args, capture_output=True, timeout=25, **kwargs)
    except (OSError, subprocess.TimeoutExpired):
        raise Stop("A local prerequisite failed or timed out.") from None


def git(*args):
    result = run(["git", *args])
    if result.returncode:
        raise Stop("Git could not verify the research checkout.")
    return result.stdout


def current_main():
    git("fetch", "--quiet", "origin", "main")
    main = git("rev-parse", "FETCH_HEAD").decode().strip()
    if git("ls-tree", main, "--", "STOP"):
        raise Stop("Upstream has posted STOP. Ending the session.")
    return main


def renew(lease):
    try:
        status, response = request(DESK + "beat", {"lease": lease}, "POST")
    except Stop:
        raise LeaseLost("Lease renewal could not be confirmed.") from None
    renewed = response.get("lease") if isinstance(response, dict) else None
    if (not 200 <= status < 300 or not isinstance(renewed, dict)
            or not renewed.get("expires_at") or renewed.get("id", lease) != lease
            or response.get("withdrawn")):
        raise LeaseLost(f"Lease renewal failed (HTTP {status}).")
    print("Lease renewed.")
    return monotonic() + 210


def assign():
    status, data = request(DESK + "next", {"handle": OWNER, "level": "solid", "kind": "prove"})
    if status != 200 or not isinstance(data, dict):
        raise Stop(f"Assignment unavailable (HTTP {status}).")
    if data.get("gap") is None:
        print("The desk has no available assignment.")
        return None
    lease = (data.get("lease") or {}).get("id")
    if not isinstance(lease, str) or not re.fullmatch(r"[A-Za-z0-9-]{1,64}", lease):
        raise Stop("The desk supplied no usable lease identifier.")
    return lease, data["gap"]


def describe(gap):
    if not isinstance(gap, dict) or gap.get("kind") not in (None, "check", "prove"):
        raise Stop("The response is not a proof assignment.")
    step = gap.get("id")
    if not isinstance(step, str) or not re.fullmatch(r"L-[a-z]+-[0-9]+", step):
        raise Stop("Unrecognized assignment identifier.")
    stem = step.replace("-", "_")
    path = "lean/PEqualNP/Outside/" + stem + ".lean"
    if gap.get("file") != path or gap.get("module") != "PEqualNP.Outside." + stem:
        raise Stop("Assignment path and module disagree.")
    statement = gap.get("statement")
    imports = gap.get("imports") or []
    if (not isinstance(statement, str) or not 1 <= len(statement) <= 20000
            or not isinstance(imports, list) or len(imports) > 64
            or not all(isinstance(m, str) and MODULE.fullmatch(m) for m in imports)):
        raise Stop("Invalid posted statement or imports.")
    for name, value in (("Step", step), ("File", path), ("Imports", imports), ("Statement", statement)):
        print(name + " " + json.dumps(value, ensure_ascii=True))
    print("Proof branch must be based on upstream main, not the session branch.")
    return step, path


def guard_statement(gap):
    # Reuse the pinned official client's complete standalone Python guard.
    # The program comes from the repository. The desk's data only goes to stdin.
    start = "guard_py() { cat <<'PY'\n"
    code = Path("tools/pnp.sh").read_text(encoding="utf-8")
    if code.count(start) != 1:
        raise Stop("The pinned client's statement guard is unavailable.")
    guard, sep, _ = code.split(start, 1)[1].partition("\nPY\n}")
    if not sep:
        raise Stop("The pinned client's statement guard has changed shape.")
    guard += "\ng = json.load(sys.stdin); sys.exit(bool(why(g['statement']) or imports_why(g.get('imports'))))"
    outcome = run([sys.executable, "-I", "-c", guard], input=json.dumps(gap).encode())
    if outcome.returncode:
        raise Stop("The pinned client's official guard refused the desk assignment.")


def encrypted_receipt(lease):
    key = Path(__file__).resolve().with_name("receipt-public.pem")
    result = run(["openssl", "pkeyutl", "-encrypt", "-pubin", "-inkey", str(key),
                  "-pkeyopt", "rsa_padding_mode:oaep", "-pkeyopt", "rsa_oaep_md:sha256",
                  "-pkeyopt", "rsa_mgf1_md:sha256"], input=lease.encode())
    if result.returncode:
        raise Stop("Could not encrypt the private lease receipt.")
    return base64.b64encode(result.stdout).decode()


def head(step):
    line = git("ls-remote", "--heads", FORK_URL, "refs/heads/" + step).split()
    if not line:
        return None
    if len(line) != 2 or not re.fullmatch(rb"[0-9a-f]{40}", line[0]):
        raise Stop("Unexpected proof branch response.")
    return line[0].decode()


def candidate(step, path, commit, latest_main, pinned):
    git("fetch", "--quiet", FORK_URL, "refs/heads/" + step)
    if git("rev-parse", "FETCH_HEAD").decode().strip() != commit:
        return None  # The branch moved during this fetch.
    diff = git("diff", "--name-status", latest_main + "..." + commit)
    mode = git("ls-tree", commit, "--", path).split()
    if (diff != f"A\t{path}\n".encode() or len(mode) != 4 or mode[:2] != [b"100644", b"blob"]
            or git("ls-tree", pinned, "--", path) or git("ls-tree", latest_main, "--", path)):
        print("Candidate rejected. The branch must add just the ordinary assigned file.")
        return None
    blob = mode[2].decode()
    if not 1 <= int(git("cat-file", "-s", blob)) <= LIMIT:
        print("Candidate rejected. The file has an invalid size.")
        return None
    content = git("cat-file", "blob", blob)
    try:
        content.decode("utf-8")
    except UnicodeDecodeError:
        print("Candidate rejected. The file must be UTF-8.")
        return None
    return content


def matching_pr(step, commit, lease):
    url = "https://api.github.com/repos/" + UPSTREAM + "/pulls"
    status, rows = request(url, {"state": "all", "head": OWNER + ":" + step, "base": "main", "per_page": 10})
    if status != 200 or not isinstance(rows, list):
        print(f"Pull request verification unavailable (HTTP {status}).")
        return None
    for pr in rows:
        h = pr["head"]
        if (h["sha"] == commit and h["ref"] == step and (h["repo"] or {}).get("full_name") == FORK
                and pr["title"] == step and pr["user"]["login"] == OWNER
                and (pr["state"] == "open" or pr["merged_at"])
                and f"Lease: {lease}" in (pr["body"] or "").splitlines()):
            return pr["number"]
    return None


def exact_header(content, gap):
    normalized = " ".join(content.decode().split())
    header = f"theorem {gap['module']} : ({gap['statement']}) := by"
    return " ".join(header.split()) in normalized


def check_command(args, cwd, deadline, beat, expect_accept=False):
    with tempfile.TemporaryFile() as log:
        proc = subprocess.Popen(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while proc.poll() is None:
                if monotonic() >= deadline:
                    raise Stop("Session time expired during validation.")
                beat()
                sleep(4)
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
        log.seek(max(0, log.tell() - 12000))
        tail = log.read().decode("utf-8", "replace")
        accepted = any(line.startswith("ACCEPTED (check)") for line in tail.splitlines())
        if proc.returncode or (expect_accept and not accepted):
            print("Check output " + json.dumps(tail))
            return False
        return True


def set_output(name):
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as output:
        print(name + "=true", file=output)


def acquire():
    if CUTOFF - time() < 42 * 60:
        raise Stop("Weekly cutoff is too close for a new assignment.")
    pinned = git("rev-parse", "HEAD").decode().strip()
    current_main()
    assignment = assign()
    if assignment is None:
        return
    lease, gap = assignment
    # Only this runner can read this file. No GitHub artifact includes it.
    state = {"lease": lease, "deadline": min(time() + 36 * 60, CUTOFF - 60)}
    private = temp_file("proof-session-private.json")
    with os.fdopen(os.open(private, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), "w") as stream:
        json.dump(state, stream)
    if lease in json.dumps(gap):
        raise Stop("Desk metadata unexpectedly contains private lease data.")
    if not isinstance(gap, dict):
        raise Stop("Invalid assignment type.")
    guard_statement(gap)
    step, path = describe(gap)
    if git("ls-tree", pinned, "--", path):
        raise Stop("The pinned upstream tree already has the assignment file.")
    renew(lease)
    public = {key: gap[key] for key in ("id", "file", "module", "statement")}
    public.update(imports=gap.get("imports") or [], upstream=pinned)
    temp_file(ARTIFACT_ASSIGN).write_text(json.dumps(public, ensure_ascii=False, indent=2), encoding="utf-8")
    (Path(".pnp")).mkdir(exist_ok=True)
    Path(".pnp", step + ".json").write_text(json.dumps({"gap": public}), encoding="utf-8")
    temp_file("proof-session-statement.txt").write_text(gap["statement"], encoding="utf-8")
    set_output("assigned")


def session():
    private = json.loads(temp_file("proof-session-private.json").read_text())
    gap = json.loads(temp_file(ARTIFACT_ASSIGN).read_text(encoding="utf-8"))
    deadline = monotonic() + max(0, min(private["deadline"], CUTOFF - 60) - time())
    return private["lease"], gap, deadline


def require_open(path):
    main = current_main()
    if git("ls-tree", main, "--", path):
        raise Stop("The assignment file is already on latest upstream main.")
    return main


def build():
    lease, gap, deadline = session()
    step, path = gap["id"], gap["file"]
    next_beat = 0

    def beat(force=False):
        nonlocal next_beat
        if force or monotonic() >= next_beat:
            main = require_open(path)
            next_beat = renew(lease)
            return main

    tested = None
    attempts = 0
    while monotonic() < deadline:
        beat()
        commit = head(step)
        if commit != tested:
            tested, attempts = commit, 0
        if commit and attempts < 2:
            attempts += 1
            main = require_open(path)
            proof = candidate(step, path, commit, main, gap["upstream"])
            if proof and not exact_header(proof, gap):
                print("Candidate rejected. Keep the theorem header from the official skeleton.")
                proof = None
                attempts = 2
            if proof:
                Path(path).write_bytes(proof)
                if check_command(["bash", "tools/pnp.sh", "check", step], ".", deadline, beat):
                    if Path(path).read_bytes() != proof:
                        print("The checker normalized the file. Commit the comment-free bytes and retry.")
                        attempts = 2
                    elif check_command(["node", "tools/check-lean.mjs", path,
                                        str(temp_file("proof-session-statement.txt")), "check"],
                                       ".", deadline, beat, expect_accept=True):
                        if head(step) != commit:
                            continue
                        beat(force=True)
                        ready = dict(step=step, commit=commit, upstream=gap["upstream"],
                                     sha256=hashlib.sha256(proof).hexdigest(), renewed_utc=timestamp(),
                                     encrypted_receipt=encrypted_receipt(lease))
                        temp_file(ARTIFACT_READY).write_text(json.dumps(ready, indent=2), encoding="utf-8")
                        print("SUBMIT READY " + ready["renewed_utc"] + " " + commit)
                        set_output("ready")
                        return
        sleep(min(25, max(0, deadline - monotonic())))
    raise Stop("Assignment window expired.")


def confirm():
    lease, gap, deadline = session()
    step, path = gap["id"], gap["file"]
    receipt = json.loads(temp_file(ARTIFACT_READY).read_text())
    commit = receipt["commit"]
    next_ready = 0
    while monotonic() < deadline:
        number = matching_pr(step, commit, lease)
        if number is not None:
            print(f"Confirmed upstream pull request {number}.")
            close("submitted")
            return
        if head(step) != commit:
            raise Stop("The checked proof branch moved; the receipt is stale.")
        if monotonic() >= next_ready:
            require_open(path)
            renew(lease)
            print("SUBMIT READY " + timestamp() + " " + commit)
            next_ready = monotonic() + 60
        sleep(min(25, max(0, deadline - monotonic())))
    raise Stop("Assignment window expired.")


def close(reason):
    private = temp_file("proof-session-private.json")
    if private.exists():
        lease = json.loads(private.read_text())["lease"]
        status, _ = request(DESK + "release", {"lease": lease, "reason": reason}, "POST")
        print(f"Desk release {reason}, HTTP {status}.")
        if not 200 <= status < 300 and status != 410:
            raise Stop("Desk did not confirm release.")
        private.unlink()


def main():
    if (os.environ.get("GITHUB_REPOSITORY") != FORK
            or os.environ.get("GITHUB_ACTOR") != OWNER
            or os.environ.get("GITHUB_REF") != "refs/heads/proof-research-session"):
        raise Stop("This job runs only on its owner's designated fork and branch.")
    if len(sys.argv) != 2 or sys.argv[1] not in ("acquire", "build", "confirm", "cleanup"):
        raise Stop("Unknown workflow phase.")
    commands = {"acquire": acquire, "build": build, "confirm": confirm, "cleanup": lambda: close("out_of_time")}
    commands[sys.argv[1]]()


if __name__ == "__main__":
    def interrupted(signum, frame):
        raise Stop("Session interrupted.")
    signal.signal(signal.SIGTERM, interrupted)
    try:
        main()
    except LeaseLost as exc:
        # No further work or publish is permitted after an unconfirmed renewal.
        # An abandoned lease expires automatically if the service was unreachable.
        temp_file("proof-session-private.json").unlink(missing_ok=True)
        raise SystemExit(str(exc)) from None
    except Stop as exc:
        raise SystemExit(str(exc)) from None
