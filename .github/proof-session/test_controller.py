"""Offline regressions. No desk, git service, real lease, or GitHub credentials."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
import hashlib
import shutil
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("proof_worker", HERE / "proof-session-worker.py")
w = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w)
STEP = "L-test-17"
OLD, NEW = "a" * 40, "b" * 40
GAP = dict(id=STEP, file="lean/PEqualNP/Outside/L_test_17.lean",
           module="PEqualNP.Outside.L_test_17", statement="True", imports=["PEqualNP.Defs"])


class Controller(unittest.TestCase):
    def setUp(self):
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        directory = self.stack.enter_context(tempfile.TemporaryDirectory())
        self.root = Path(directory)
        self.stack.enter_context(contextlib.chdir(self.root))
        self.stack.enter_context(patch.dict(os.environ, {
            "RUNNER_TEMP": directory, "GITHUB_OUTPUT": str(self.root / "output"),
            "PNP_CHECKED_STEP": "", "PNP_CHECKED_COMMIT": ""}))
        Path(GAP["file"]).parent.mkdir(parents=True)
        self.http = self.stub("request", side_effect=AssertionError("Unexpected HTTP call"))
        self.stub("sleep")

    def stub(self, name, **kwargs):
        return self.stack.enter_context(patch.object(w, name, **kwargs))

    def api(self, *results):
        self.http.side_effect = list(results)

    def private(self, reason=None):
        state = dict(lease="PRIVATE-TEST-ID", deadline=w.time() + 9000)
        if reason: state["release_reason"] = reason
        p = w.temp_file("proof-session-private.json")
        p.write_text(json.dumps(state))
        return p

    def test_ordinary_expiry_stops_unfinished_work(self):
        self.api((410, {"error": "expired"}))
        with self.assertRaises(w.LeaseLost): w.renew("private")

    def test_checked_expiry_and_explicit_withdrawal(self):
        self.api((410, {"error": "expired"}), (410, {"withdrawn": True}), (200, {"withdrawn": True}))
        self.assertEqual(w.renew("private", checked=True), "not_renewed")
        for _ in range(2):
            with self.assertRaisesRegex(w.LeaseLost, "withdrew"): w.renew("private", checked=True)

    def test_checked_offline_retries_and_stops_on_late_withdrawal(self):
        self.api(w.Stop("network"), (503, None), (410, {"withdrawn": True}))
        with self.assertRaises(w.LeaseLost): w.renew("private", checked=True)
        self.assertEqual(self.http.call_count, 3)
        self.api(*[(503, None)]*4)
        self.assertEqual(w.renew("private", checked=True), "unconfirmed")

    def test_selection_requires_complete_preexisting_evidence(self):
        self.assertIsNone(w.proof_of_evidence(OLD))
        for step, commit in [(STEP, ""), ("", OLD), ("../x", OLD), (STEP, "master")]:
            with patch.dict(os.environ, {"PNP_CHECKED_STEP":step,"PNP_CHECKED_COMMIT":commit}):
                with self.assertRaises(w.Stop): w.proof_of_evidence(OLD)
        self.http.assert_not_called()

    def preflight_fixture(self):
        os.environ.update(PNP_CHECKED_STEP=STEP,PNP_CHECKED_COMMIT=NEW)
        self.stub("public_row",return_value=GAP)
        self.stub("guard_statement")
        self.stub("head",return_value=NEW)
        self.stub("require_open",return_value=OLD)
        self.stub("candidate",return_value=b"theorem PEqualNP.Outside.L_test_17 : True := True.intro\n")
        self.stub("guarded_candidate",return_value=True)
        self.stub("time",return_value=w.CUTOFF-10000)

    def test_proof_of_checks_exact_input_before_any_lease(self):
        self.preflight_fixture()
        def exact(args, cwd, deadline, poll, expect_accept):
            self.assertTrue(expect_accept)
            self.assertEqual(Path(args[2]).read_bytes(),w.candidate.return_value)
            self.assertEqual(Path(args[3]).read_text(),GAP["statement"])
            self.assertTrue(w.guarded_candidate.called)
            poll()
            return True
        self.stub("check_command",side_effect=exact)
        result=w.proof_of_evidence(OLD)
        self.assertEqual(result,{"id":STEP,"commit":NEW,"descriptor":w.descriptor(GAP)})
        self.assertFalse(Path(GAP["file"]).exists())
        self.http.assert_not_called()

    def test_failures_in_each_preflight_gate_prevent_targeted_next(self):
        self.preflight_fixture()
        checker=self.stub("check_command",return_value=False)
        with self.assertRaises(w.Stop): w.proof_of_evidence(OLD)
        self.assertFalse(Path(GAP["file"]).exists())
        self.assertTrue(checker.called)
        checker.reset_mock()
        w.guarded_candidate.return_value=False
        with self.assertRaisesRegex(w.Stop,"file guard"): w.proof_of_evidence(OLD)
        checker.assert_not_called()
        self.http.assert_not_called()

    def test_targeted_request_uses_exact_upstream_parameters(self):
        self.stub("current_main", return_value=OLD)
        self.stub("head", return_value=NEW)
        self.stub("time", return_value=w.CUTOFF-10000)
        self.stub("public_row",return_value=GAP)
        self.stub("require_open",return_value=OLD)
        self.api((200, {"gap":GAP, "lease":{"id":"fake-id"}}))
        self.assertEqual(w.assign({"id":STEP,"commit":NEW,"descriptor":w.descriptor(GAP)}), ("fake-id", GAP))
        w.require_open.assert_called_once_with(GAP["file"],STEP,need_known=True)
        self.assertEqual(self.http.call_args.args, (w.DESK+"next",{
            "handle":w.OWNER,"value":"1","gap":STEP,"have":"proof"}))

    def test_default_assignment_never_claims_to_have_proof(self):
        self.stub("current_main", return_value=OLD)
        self.stub("time", return_value=w.CUTOFF-10000)
        self.api((200, {"gap":None,"note":"No work"}), (200, {"gap":GAP,"lease":{"id":"fake-id"}}))
        w.assign()
        first, second = [call.args[1] for call in self.http.call_args_list]
        self.assertEqual(first, {"handle":w.OWNER,"value":"1","kind":"prove"})
        self.assertEqual(second, dict(first, hard="1"))

    def test_moved_target_or_weekly_cutoff_never_acquires(self):
        self.stub("current_main", return_value=OLD)
        self.stub("head", return_value=NEW)
        clock = self.stub("time", return_value=w.CUTOFF-10000)
        with self.assertRaises(w.Stop): w.assign({"id":STEP,"commit":OLD})
        clock.return_value = w.CUTOFF-60
        with self.assertRaises(w.Stop): w.assign()
        self.http.assert_not_called()

    def test_authoritative_guard_accepts_valid_alternate_header_and_refuses_disallowed_code(self):
        fixture=HERE/"reference-pnp.sh"
        self.assertTrue(fixture.exists())
        raw=fixture.read_bytes()
        self.assertEqual(hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest(),
                         "ff5542351b61744c6487f580d4689c7cf76f32c3")
        Path("tools").mkdir()
        shutil.copyfile(fixture,"tools/pnp.sh")
        w.guard_statement(GAP)
        source=b"import PEqualNP.Defs\n\ntheorem PEqualNP.Outside.L_test_17 : True := True.intro\n"
        self.assertTrue(w.guarded_candidate(source,GAP["file"],GAP,self.root))
        self.assertFalse(w.guarded_candidate(source + b"\n#eval 3\n",GAP["file"],GAP,self.root))
        self.assertFalse(w.guarded_candidate(b"-- normalize me\n"+source,GAP["file"],GAP,self.root))

    def test_targeted_descriptor_drift_or_ambiguous_state_never_claims(self):
        self.stub("time",return_value=w.CUTOFF-10000)
        self.stub("current_main",return_value=OLD)
        self.stub("head",return_value=NEW)
        self.stub("git",return_value=b"")
        self.stub("public_row",return_value=dict(GAP,statement="False"))
        evidence={"id":STEP,"commit":NEW,"descriptor":w.descriptor(GAP)}
        with self.assertRaisesRegex(w.Stop,"statement changed"): w.assign(evidence)
        self.http.assert_not_called()
        w.public_row.return_value=GAP
        self.api((503,{"state":"open"}))
        with self.assertRaisesRegex(w.Stop,"did not confirm"): w.assign(evidence)
        self.assertTrue(all(c.args[0] != w.DESK+"next" for c in self.http.call_args_list))

    def test_rows_use_separate_detail_and_live_status(self):
        self.api((200,{"gaps":[dict(GAP,id="L-test-18"),GAP]}),
                 (200,{"gaps":[GAP,GAP]}), (200, {"state":"resolved"}))
        self.assertEqual(w.public_row(STEP), GAP)
        with self.assertRaises(w.Stop): w.public_row(STEP)
        self.stub("current_main", return_value=OLD)
        self.stub("git", return_value=b"")
        with self.assertRaisesRegex(w.Stop,"no longer open"): w.require_open(GAP["file"],STEP)

    def test_issued_mismatch_is_released_and_never_researched(self):
        self.stub("git", return_value=OLD.encode())
        self.stub("proof_of_evidence", return_value={"descriptor":w.descriptor(GAP)})
        self.stub("assign", return_value=("private",dict(GAP,statement="False")))
        with self.assertRaisesRegex(w.Stop,"differs"): w.acquire()
        self.api((200,{}))
        w.cleanup()
        self.assertEqual(self.http.call_args.args[1],{"lease":"private","reason":"other"})
        self.assertFalse(w.temp_file("proof-session-private.json").exists())

    def test_session_duration_and_cutoff(self):
        self.stub("git", side_effect=[OLD.encode(),b""])
        self.stub("proof_of_evidence", return_value=None)
        self.stub("assign", return_value=("private",GAP))
        self.stub("guard_statement")
        self.stub("renew")
        clock=self.stub("time", return_value=w.CUTOFF-12000)
        w.acquire()
        path=w.temp_file("proof-session-private.json")
        self.assertEqual(json.loads(path.read_text())["deadline"],clock.return_value+9000)
        path.unlink()
        w.git.side_effect=[OLD.encode(),b""]
        clock.return_value=w.CUTOFF-2200
        w.acquire()
        self.assertEqual(json.loads(path.read_text())["deadline"],w.CUTOFF-60)

    def test_moved_candidate_keeps_lease_and_only_certifies_new_sha(self):
        self.stub("session",return_value=("private",dict(GAP,upstream=OLD),w.monotonic()+60))
        self.stub("require_open",return_value=OLD)
        renew=self.stub("renew",return_value="renewed")
        self.stub("head",side_effect=[OLD]+[NEW]*12)
        self.stub("candidate",side_effect=[b"old bytes",b"new bytes"])
        self.stub("encrypted_receipt",return_value="opaque")
        self.stub("check_command",side_effect=lambda args,cwd,deadline,poll,**kw: (poll() or True))
        w.build()
        receipt=json.loads(w.temp_file(w.ARTIFACT_READY).read_text())
        self.assertEqual(receipt["commit"],NEW)
        self.assertEqual(receipt["sha256"],w.hashlib.sha256(b"new bytes").hexdigest())
        self.assertNotIn("private",str(receipt))
        self.assertEqual(renew.call_count,2)
        self.http.assert_not_called()

    def test_changed_checked_branch_revalidates_before_matching_pr(self):
        self.stub("session",return_value=("private",dict(GAP,upstream=OLD),w.monotonic()+60))
        ready=w.temp_file(w.ARTIFACT_READY)
        ready.write_text(json.dumps({"commit":OLD}))
        self.stub("matching_pr",side_effect=[None,None,317])
        self.stub("head",return_value=NEW)
        self.stub("build",side_effect=lambda:ready.write_text(json.dumps({"commit":NEW})))
        self.stub("close")
        w.confirm()
        self.assertEqual([c.args[1] for c in w.matching_pr.call_args_list],[OLD,OLD,NEW])
        w.close.assert_called_once_with("submitted")

    def test_merge_between_pr_poll_and_closed_row_records_submission(self):
        self.stub("session",return_value=("private",dict(GAP,upstream=OLD),w.monotonic()+60))
        w.temp_file(w.ARTIFACT_READY).write_text(json.dumps({"commit":NEW}))
        self.stub("matching_pr",side_effect=[None,317])
        self.stub("head",return_value=NEW)
        self.stub("require_open",side_effect=w.StepClosed("upstream now contains this file"))
        self.stub("close")
        w.confirm()
        w.close.assert_called_once_with("submitted")

    def test_private_cleanup_preserves_submitted_reason_after_network_failure(self):
        private=self.private()
        self.api(w.Stop("network"),(200,{}))
        with self.assertRaises(w.Stop): w.close("submitted")
        self.assertEqual(json.loads(private.read_text())["release_reason"],"submitted")
        w.cleanup()
        self.assertEqual(self.http.call_args.args[1]["reason"],"submitted")
        self.assertFalse(private.exists())

    def test_final_failed_release_erases_private_state(self):
        private=self.private()
        self.api((503,None))
        with self.assertRaises(w.Stop): w.cleanup()
        self.assertFalse(private.exists())

    def test_checker_failure_does_not_log_private_diagnostics(self):
        fake=Mock(pid=1234, returncode=1)
        fake.poll.return_value=1
        def start(args, **kwargs):
            kwargs["stdout"].write(b"untrusted text containing PRIVATE-TEST-ID and workflow commands")
            return fake
        with patch.object(w.subprocess,"Popen",side_effect=start), \
             patch.object(w.os,"killpg",create=True) as kill, contextlib.redirect_stdout(io.StringIO()) as log:
            self.assertFalse(w.check_command(["fake"],".",w.monotonic()+60,lambda: None))
        kill.assert_not_called()
        self.assertNotIn("PRIVATE-TEST-ID",log.getvalue())

    def test_interruption_kills_and_waits_for_checker_group(self):
        fake=Mock(pid=1234)
        fake.poll.return_value=None
        lock=Path("lean/.lake/check.lock")
        def moved():
            lock.mkdir(parents=True)
            raise w.CandidateChanged
        with patch.object(w.subprocess,"Popen",return_value=fake), \
             patch.object(w.signal,"SIGKILL",9,create=True), patch.object(w.os,"killpg",create=True) as kill:
            with self.assertRaises(w.CandidateChanged):
                w.check_command(["fake"],".",w.monotonic()+60,moved,expect_accept=True)
            self.assertEqual([c.args[1] for c in kill.call_args_list],[w.signal.SIGTERM,9])
        self.assertEqual(fake.wait.call_count,2)
        self.assertFalse(lock.exists())

    def test_preexisting_checker_lock_is_preserved(self):
        lock=Path("lean/.lake/check.lock")
        lock.mkdir(parents=True)
        fake=Mock(pid=1234)
        fake.poll.return_value=None
        with patch.object(w.subprocess,"Popen",return_value=fake), patch.object(w.signal,"SIGKILL",9,create=True), \
             patch.object(w.os,"killpg",create=True):
            with self.assertRaises(w.CandidateChanged):
                w.check_command(["fake"],".",w.monotonic()+60,Mock(side_effect=w.CandidateChanged),expect_accept=True)
        self.assertTrue(lock.is_dir())

    @unittest.skipUnless(os.name=="posix","requires POSIX process groups")
    def test_real_interrupted_process_and_lock(self):
        import sys
        import time
        lock=Path("lean/.lake/check.lock")
        child = ("import pathlib, signal, sys, time\n"
                 "def on_term(*_):\n"
                 "    pathlib.Path('child-terminated').touch(); sys.exit(0)\n"
                 "signal.signal(signal.SIGTERM,on_term)\n"
                 "pathlib.Path('child-ready').touch(); time.sleep(30)\n")
        source = ("import pathlib, signal, subprocess, sys, time\n"
                  "p=pathlib.Path('lean/.lake/check.lock'); p.mkdir(parents=True)\n"
                  "child=subprocess.Popen([sys.executable,'-c',sys.argv[1]])\n"
                  "def on_term(*_):\n"
                  "    child.wait(timeout=3); p.rmdir(); pathlib.Path('checker-terminated').touch(); sys.exit(3)\n"
                  "signal.signal(signal.SIGTERM,on_term)\n"
                  "pathlib.Path('checker-ready').touch(); time.sleep(30)\n")
        def moved():
            limit=time.monotonic()+5
            markers=(lock,Path("checker-ready"),Path("child-ready"))
            while not all(p.exists() for p in markers) and time.monotonic()<limit: time.sleep(0.01)
            self.assertTrue(all(p.exists() for p in markers))
            raise w.CandidateChanged
        with self.assertRaises(w.CandidateChanged):
            w.check_command([sys.executable,"-c",source,child],".",w.monotonic()+10,moved,True)
        self.assertFalse(lock.exists())
        self.assertTrue(Path("child-terminated").exists())
        self.assertTrue(Path("checker-terminated").exists())
        replacement=("from pathlib import Path\n"
                     "p=Path('lean/.lake/check.lock'); p.mkdir(); p.rmdir(); print('ACCEPTED (check)')\n")
        self.assertTrue(w.check_command([sys.executable,"-c",replacement],".",w.monotonic()+5,lambda:None,True))


if __name__ == "__main__": unittest.main()
