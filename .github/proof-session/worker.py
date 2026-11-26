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
SESSION_SECONDS = 150 * 60
MIN_NEW_SESSION = 20 * 60
POLL_SECONDS = 25
CUTOFF = datetime(2026, 12, 2, 3, 22, 45, tzinfo=timezone.utc).timestamp()
ARTIFACT_ASSIGN = "proof-session-assignment.json"
ARTIFACT_READY = "proof-session-ready.json"
last_desk_at = 0


def temp_file(name):
    return Path(os.environ["RUNNER_TEMP"]) / name


def timestamp():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


class Stop(Exception):
    """Controlled message with no private data."""


class LeaseLost(Stop):
    pass


class StepClosed(Stop):
    pass


class CandidateChanged(Exception):
    """An owner branch revision superseded the bytes currently being checked."""


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def request(url, params, method="GET"):
    global last_desk_at
    if url.startswith(DESK):
        delay = 3 - (monotonic() - last_desk_at)
        if delay > 0:
            sleep(delay)
        last_desk_at = monotonic()
    endpoint = url + "?" + urlencode(params)
    req = Request(endpoint, method=method, headers={"User-Agent": "Brett-Snodgrass-proof-session"})
    try:
        with build_opener(NoRedirect()).open(req, timeout=15) as response:
            payload = response.read(2 * 1024 * 1024 + 1)
            if len(payload) > 2 * 1024 * 1024:
                raise Stop("Remote response exceeded the size limit.")
            return response.status, json.loads(payload)
    except HTTPError as exc:
        with exc:
            try:
                payload = exc.read(2 * 1024 * 1024 + 1)
                return exc.code, json.loads(payload) if len(payload) <= 2 * 1024 * 1024 else None
            except (ValueError, OSError):
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


def renew(lease, checked=False):
    # pnp.sh stops unfinished work on a missing lease. Its submit path permits
    # an already checked proof after ordinary expiration, but never withdrawal.
    for attempt in range(4 if checked else 1):
        try:
            status, response = request(DESK + "beat", {"lease": lease}, "POST")
        except Stop:
            status, response = 0, None
        if isinstance(response, dict) and response.get("withdrawn") is True:
            raise LeaseLost("The desk withdrew the step. Do not submit.")
        renewed = response.get("lease") if isinstance(response, dict) else None
        if (200 <= status < 300 and isinstance(renewed, dict)
                and renewed.get("id", lease) == lease):
            print("Lease renewed.")
            return "renewed"
        if not checked:
            raise LeaseLost(f"Unfinished work stopped after unconfirmed renewal (HTTP {status}).")
        if isinstance(response, dict) and 100 <= status < 500:
            print(f"Finished proof eligible for submission after a non-renewing response (HTTP {status}).")
            return "not_renewed"
        if attempt < 3:
            sleep(3)
    print("Submission renewal was unavailable after retries; the official client permits the finished proof.")
    return "unconfirmed"


def empty_queue(data):
    """Only ordinary scarcity qualifies for another request. Hold on unknown states."""
    message = data.get("error") or data.get("note") or ""
    if not isinstance(message, str):
        raise Stop("The empty-queue response contains an unexpected status.")
    if data.get("error") or data.get("lease") or any(data.get(key) for key in
            ("disabled", "paused", "blocked", "hold", "held", "leases", "active_lease",
             "existing_lease", "cooldown", "retry_after", "retry_after_seconds")):
        return False
    if data.get("status") not in (None, "ok", "empty", "no_gap", "unavailable", "all_taken", "no_match"):
        return False
    if not message.strip():
        return True
    if re.search(r"disabl|paus|limit|quota|calibrat|onboard|enroll|cooldown|hold|"
                 r"you (?:already )?(?:have|hold)|your (?:active |existing )?lease|"
                 r"existing lease|denied|forbidden|suspend|stop|register|authenticat|"
                 r"permission|credential|eligib|community|new (?:agent|user)|already|must|maintenance|"
                 r"hours?|tomorrow|do not|don.t|commands?|tools/|\bcurl\b|\bwget\b", message, re.I):
        return False
    return bool(re.search(r"\b(?:no (?:open |available |matching )?(?:steps?|gaps?|work|assignments?)|"
                          r"every (?:open )?(?:step|gap)|all (?:the )?(?:open )?(?:steps|gaps)|"
                          r"nothing (?:available|open|right now)|taken|leased out|try again|ask again|check back)\b",
                          message, re.I))


def print_public_queue_status(data):
    if not isinstance(data, dict):
        return
    for field in ("note", "error", "status"):
        value = data.get(field)
        if isinstance(value, str) and value:
            value = re.sub(r"https?://\S+|[\w.+-]+@[\w.-]+", "[redacted]", value)
            value = re.sub(r"\b[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}\b",
                           "[redacted]", value, flags=re.I)
            value = re.sub(r"\b[A-Za-z0-9_=-]{24,}\b", "[redacted]", value)
            value = re.sub(r"\b(lease|token|credential|secret)\s*[=:]\s*\S+",
                           r"\1=[redacted]", value, flags=re.I)
            print("Desk " + field + " " + json.dumps(value[:320], ensure_ascii=True))


def assign():
    choices = ("solid",)
    for attempt, level in enumerate(choices, start=1):
        if CUTOFF - time() < MIN_NEW_SESSION + 60:
            raise Stop("Weekly cutoff is too close for a new assignment.")
        current_main()
        params = {"handle": OWNER, "value": "1", "another": "1",
                  "level": level, "kind": "prove"}
        print(f"Second assignment request {attempt}/{len(choices)}: {level}, prove.")
        status, data = request(DESK + "next", params)
        if status != 200 or not isinstance(data, dict) or "gap" not in data:
            print_public_queue_status(data)
            raise Stop(f"Assignment unavailable (HTTP {status}).")
        if data["gap"] is not None:
            lease = data.get("lease")
            lease_id = lease.get("id") if isinstance(lease, dict) else None
            if not isinstance(lease_id, str) or not re.fullmatch(r"[A-Za-z0-9-]{1,64}", lease_id):
                raise Stop("The desk supplied no usable lease identifier.")
            gap = data["gap"]
            if isinstance(gap, dict) and gap.get("id") == "L-meta-17121":
                raise Stop("Desk returned the primary session's assignment. Leaving that session untouched.")
            terms = lease.get("terms") or {}
            return lease_id, gap, terms, level
        print_public_queue_status(data)
        if not empty_queue(data):
            print("Desk returned a restriction or unfamiliar status. No further requests.")
            return None
        if attempt < len(choices):
            print("Waiting three minutes before requesting another assignment.")
            sleep(180)
    print("No available assignment in the requested queue.")
    return None


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


def client_python(start):
    # These fixed, local programs come from the pinned official shell client.
    code = Path("tools/pnp.sh").read_text(encoding="utf-8")
    if code.count(start) != 1:
        raise Stop("A pinned client validation routine is unavailable.")
    body, sep, _ = code.split(start, 1)[1].partition("\nPY\n}")
    if not sep:
        raise Stop("A pinned client validation routine changed shape.")
    return body


def guard_statement(gap):
    guard = client_python("guard_py() { cat <<'PY'\n")
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


def guarded_candidate(proof, path, gap, directory):
    clean = Path(directory, "proof.lean")
    meta = Path(directory, "descriptor.json")
    clean.write_bytes(proof)
    meta.write_text(json.dumps({"gap": gap}), encoding="utf-8")
    tidy = client_python("tidy() { python3 -I - \"$1\" <<'PY'\n")
    fmt = client_python("format_py() { cat <<'PY'\n")
    if run([sys.executable, "-I", "-c", tidy, str(clean)]).returncode or clean.read_bytes() != proof:
        return False
    return run([sys.executable, "-I", "-c", fmt, str(clean), path, str(meta)]).returncode == 0


def stop_checker(proc, lock, owns_new_lock):
    # The upstream exact checker releases its empty directory lock on TERM.
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=6)
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    proc.wait()
    # This checkout is exclusive to this job. Preserve any preexisting lock,
    # symlink or nonempty directory. rmdir never recurses through owned files.
    if owns_new_lock and not lock.is_symlink():
        try:
            lock.rmdir()
        except FileNotFoundError:
            pass
        except OSError:
            raise Stop("The interrupted checker left a lock that could not be safely reclaimed.") from None


def check_command(args, cwd, deadline, beat, expect_accept=False):
    lock = Path(cwd, "lean/.lake/check.lock")
    owns_new_lock = expect_accept and not os.path.lexists(lock)
    with tempfile.TemporaryFile() as log:
        proc = subprocess.Popen(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while proc.poll() is None:
                if monotonic() >= deadline:
                    raise Stop("Session time expired during validation.")
                beat()
                sleep(4)
        except BaseException:
            stop_checker(proc, lock, owns_new_lock)
            raise
        log.seek(max(0, log.tell() - 12000))
        tail = log.read().decode("utf-8", "replace")
        if proc.returncode == 120 or any(line.startswith("STOPPED by a notice on the proofs repository")
                                         for line in tail.splitlines()):
            raise Stop("The official client reported upstream STOP. Ending the session.")
        if not expect_accept and proc.returncode == 3:
            raise Stop("The official client stopped work on this step.")
        accepted = any(line.startswith("ACCEPTED (check)") for line in tail.splitlines())
        if proc.returncode or (expect_accept and not accepted):
            # The proof controls some diagnostics. Don't copy them into public
            # logs, GitHub workflow command channels, output names, or artifacts.
            print(f"Candidate check failed (exit {proc.returncode}).")
            return False
        return True


def set_output(name):
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as output:
        print(name + "=true", file=output)


def watch_revision(step, commit, beat):
    next_poll = 0

    def poll():
        nonlocal next_poll
        beat()
        if monotonic() >= next_poll:
            if head(step) != commit:
                raise CandidateChanged
            next_poll = monotonic() + POLL_SECONDS

    return poll


def acquire():
    pinned = git("rev-parse", "HEAD").decode().strip()
    assignment = assign()
    if assignment is None:
        return
    lease, gap, terms, requested_level = assignment
    # Only this runner can read this file. No GitHub artifact includes it.
    state = {"lease": lease, "deadline": min(time() + SESSION_SECONDS, CUTOFF - 60),
             "release_reason": "other"}
    private = temp_file("proof-session-private.json")
    with os.fdopen(os.open(private, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), "w") as stream:
        json.dump(state, stream)
    if lease in json.dumps(gap):
        raise Stop("Desk metadata unexpectedly contains private lease data.")
    if not isinstance(gap, dict):
        raise Stop("Invalid assignment type.")
    if not isinstance(terms, dict) or terms.get("level", requested_level) != requested_level or terms.get("kind", "prove") not in ("prove", "check"):
        raise Stop("The issued lease terms differ from the requested level or kind. Returning it.")
    if gap.get("level", requested_level) != requested_level:
        raise Stop("The returned row differs from the requested level. Returning it.")
    guard_statement(gap)
    step, path = describe(gap)
    if git("ls-tree", pinned, "--", path):
        raise Stop("The pinned upstream tree already has the assignment file.")
    renew(lease)
    state["release_reason"] = "out_of_time"
    private.write_text(json.dumps(state), encoding="utf-8")
    public = {key: gap[key] for key in ("id", "file", "module", "statement")}
    public.update(imports=gap.get("imports") or [], upstream=pinned)
    public.update(level=requested_level, kind="prove")
    if type(terms.get("points")) is int:
        public["points"] = terms["points"]
    print("Assignment level " + requested_level + ", kind prove.")
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


def require_open(path, step=None, need_known=False):
    main = current_main()
    if git("ls-tree", main, "--", path):
        raise StepClosed("The assignment file is already on latest upstream main.")
    if step is not None:
        try:
            status, row = request(DESK + "step", {"gap": step})
            if not 200 <= status < 300:
                row = None
        except Stop:
            row = None
        state = row.get("state") if isinstance(row, dict) else None
        if isinstance(state, str) and state not in ("open", "leased"):
            raise StepClosed("The desk reports that the assignment is no longer open.")
        if need_known and state not in ("open", "leased"):
            raise Stop("The desk did not confirm the targeted step is still open. No lease requested.")
    return main


def build():
    lease, gap, deadline = session()
    step, path = gap["id"], gap["file"]
    next_beat = 0

    def beat():
        nonlocal next_beat
        if monotonic() >= next_beat:
            require_open(path, step)
            renew(lease)
            next_beat = monotonic() + 210

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
            if proof:
                Path(path).write_bytes(proof)
                poll = watch_revision(step, commit, beat)
                try:
                    if check_command(["bash", "tools/pnp.sh", "check", step], ".", deadline, poll):
                        if Path(path).read_bytes() != proof:
                            print("The checker normalized the file. Commit the comment-free bytes and retry.")
                            attempts = 2
                        elif check_command(["node", "tools/check-lean.mjs", path,
                                            str(temp_file("proof-session-statement.txt")), "check"],
                                           ".", deadline, poll, expect_accept=True):
                            if head(step) != commit:
                                continue
                            require_open(path, step)
                            status = renew(lease, checked=True)
                            if head(step) != commit:
                                if status != "renewed":
                                    raise LeaseLost("The checked revision moved without an active lease. Do not submit.")
                                continue
                            checked_utc = timestamp()
                            ready = dict(step=step, commit=commit, upstream=gap["upstream"],
                                         sha256=hashlib.sha256(proof).hexdigest(), checked_utc=checked_utc,
                                         renewed_utc=checked_utc if status == "renewed" else None,
                                         lease_status=status, encrypted_receipt=encrypted_receipt(lease))
                            temp_file(ARTIFACT_READY).write_text(json.dumps(ready, indent=2), encoding="utf-8")
                            print("SUBMIT READY " + ready["checked_utc"] + " " + commit)
                            set_output("ready")
                            return
                except CandidateChanged:
                    print("Candidate revision changed. Stopped the superseded checker; continuing this assignment.")
                    continue
        sleep(min(POLL_SECONDS, max(0, deadline - monotonic())))
    raise Stop("Assignment window expired.")


def confirm():
    lease, gap, deadline = session()
    step, path = gap["id"], gap["file"]
    receipt = json.loads(temp_file(ARTIFACT_READY).read_text())
    commit = receipt["commit"]
    next_ready = next_pr = 0

    def submitted():
        number = matching_pr(step, commit, lease)
        if number is None:
            return False
        print(f"Confirmed upstream pull request {number}.")
        close("submitted")
        return True

    while monotonic() < deadline:
        if monotonic() >= next_pr:
            if submitted():
                return
            next_pr = monotonic() + 75
        if head(step) != commit:
            if submitted():
                return
            print("Checked branch changed before submission. Revalidating the new revision on this assignment.")
            build()
            commit = json.loads(temp_file(ARTIFACT_READY).read_text())["commit"]
            next_ready = next_pr = 0
            continue
        if monotonic() >= next_ready:
            try:
                require_open(path, step)
            except StepClosed:
                if submitted():
                    return
                raise
            renew(lease, checked=True)
            print("SUBMIT READY " + timestamp() + " " + commit)
            next_ready = monotonic() + 60
        sleep(min(25, max(0, deadline - monotonic())))
    raise Stop("Assignment window expired.")


def close(reason, final=False):
    private = temp_file("proof-session-private.json")
    if private.exists():
        lease = json.loads(private.read_text())["lease"]
        try:
            status, _ = request(DESK + "release", {"lease": lease, "reason": reason}, "POST")
            print(f"Desk release {reason}, HTTP {status}.")
            if not 200 <= status < 300 and status != 410:
                raise Stop("Desk did not confirm release.")
        except Stop:
            if not final:
                # Cleanup must retry the original reason if a submitted release
                # fails, rather than marking the accepted submission out of time.
                state = json.loads(private.read_text())
                state["release_reason"] = reason
                private.write_text(json.dumps(state), encoding="utf-8")
            raise
        else:
            private.unlink(missing_ok=True)
        finally:
            if final:
                private.unlink(missing_ok=True)


def cleanup():
    private = temp_file("proof-session-private.json")
    if private.exists():
        try:
            reason = json.loads(private.read_text()).get("release_reason", "out_of_time")
            close(reason, final=True)
        finally:
            private.unlink(missing_ok=True)


def main():
    if (os.environ.get("GITHUB_REPOSITORY") != FORK
            or os.environ.get("GITHUB_ACTOR") != OWNER
            or os.environ.get("GITHUB_REF") != "refs/heads/proof-research-second"):
        raise Stop("This job runs only on its owner's designated fork and branch.")
    if len(sys.argv) != 2 or sys.argv[1] not in ("acquire", "build", "confirm", "cleanup"):
        raise Stop("Unknown workflow phase.")
    commands = {"acquire": acquire, "build": build, "confirm": confirm, "cleanup": cleanup}
    commands[sys.argv[1]]()


if __name__ == "__main__":
    def interrupted(signum, frame):
        raise Stop("Session interrupted.")
    signal.signal(signal.SIGTERM, interrupted)
    try:
        main()
    except StepClosed as exc:
        private = temp_file("proof-session-private.json")
        if private.exists():
            state = json.loads(private.read_text())
            state["release_reason"] = "other"
            private.write_text(json.dumps(state), encoding="utf-8")
        raise SystemExit(str(exc)) from None
    except LeaseLost as exc:
        # End this phase immediately. The unconditional cleanup step can still
        # release this particular lease on a transient outage and erase it.
        raise SystemExit(str(exc)) from None
    except Stop as exc:
        raise SystemExit(str(exc)) from None
