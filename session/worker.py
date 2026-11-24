import hashlib
import json
import os
import pathlib
import re
import subprocess
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

DESK = "https://pequalnp.com/desk/"
RAW = "https://raw.githubusercontent.com/DavidFreeborn/pequalnp-proofs/codex/proof-checking/session/"
ROOT = pathlib.Path("project").resolve()
DEADLINE = time.monotonic() + 70 * 60

def request(url, post=False):
    req = urllib.request.Request(url, method="POST" if post else "GET",
                                 headers={"User-Agent": "DavidFreeborn-PNP-proof-session"})
    with urllib.request.urlopen(req, timeout=30) as response:
        return json.load(response)

def local_file(name):
    try:
        return request(RAW + name + "?t=" + str(int(time.time())))
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return None
        raise

def lease_action(action, lease, reason=None):
    params = {"lease": lease}
    if reason:
        params["reason"] = reason
    return request(DESK + action + "?" + urllib.parse.urlencode(params), post=True)

def run_check(command, gap, stop):
    log = pathlib.Path(os.environ["RUNNER_TEMP"]) / "candidate-check.log"
    with log.open("w") as output:
        process = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        while process.poll() is None:
            if stop.wait(5) or time.monotonic() > DEADLINE:
                import signal
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                return False
    text = log.read_text(errors="replace")
    print("CHECK_RESULT", gap, process.returncode, flush=True)
    print(text[-16000:], flush=True)
    return process.returncode == 0

while time.monotonic() < DEADLINE:
    assignment = request(DESK + "next?handle=DavidFreeborn")
    gap = assignment.get("gap")
    if gap is None:
        print("NO_STEP", assignment.get("note", assignment.get("error", "")), flush=True)
        break
    lease = assignment["lease"]["id"]
    gid, path, module = gap["id"], gap["file"], gap["module"]
    if (not re.fullmatch(r"L-[a-z]+-[0-9]+", gid)
            or not re.fullmatch(r"lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean", path)
            or not re.fullmatch(r"PEqualNP\.Outside\.[A-Za-z0-9_]+", module)):
        lease_action("release", lease, "other")
        raise RuntimeError("Unexpected assignment shape")
    print("ASSIGNMENT", json.dumps({"gap": gap, "base_sha": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()}, ensure_ascii=False), flush=True)
    summary = pathlib.Path(os.environ["GITHUB_STEP_SUMMARY"])
    with summary.open("a") as output:
        output.write("\n### " + gid + "\n\n" + gap.get("title", "") + "\n\n")
        output.write("\u0060\u0060\u0060lean\n" + gap["statement"] + "\n\u0060\u0060\u0060\n")
    stop = threading.Event()
    def renew():
        while not stop.wait(5 * 60):
            try:
                lease_action("beat", lease)
                print("LEASE_RENEWED", gid, flush=True)
            except urllib.error.HTTPError as error:
                print("LEASE_HTTP_ERROR", error.code, flush=True)
                if error.code == 410:
                    stop.set()
                    return
            except Exception:
                print("LEASE_RENEWAL_NETWORK_ERROR", flush=True)
    thread = threading.Thread(target=renew, daemon=True)
    thread.start()
    released = False
    last = None
    try:
        while not stop.is_set() and time.monotonic() < DEADLINE:
            control = local_file("control.json")
            if control and control.get("gap") == gid:
                reason = control.get("reason")
                if reason in {"submitted", "out_of_time", "other", "missing_lemma",
                              "does_not_elaborate", "statement_seems_false", "hypothesis_too_weak"}:
                    lease_action("release", lease, reason)
                    released = True
                    print("RELEASED", gid, reason, flush=True)
                    break
            candidate = local_file("candidate.json")
            if candidate and candidate.get("gap") == gid:
                proof = candidate.get("proof", "")
                digest = hashlib.sha256(proof.encode()).hexdigest()
                if digest != last:
                    last = digest
                    if len(proof.encode()) > 512 * 1024:
                        print("CANDIDATE_TOO_LARGE", gid, flush=True)
                        continue
                    target = ROOT / path
                    if target.exists():
                        print("ASSIGNMENT_FILE_ALREADY_EXISTS", gid, flush=True)
                        lease_action("release", lease, "does_not_elaborate")
                        released = True
                        break
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text(proof)
                    statement = pathlib.Path(os.environ["RUNNER_TEMP"]) / "statement.txt"
                    statement.write_text(gap["statement"])
                    imports = pathlib.Path(os.environ["RUNNER_TEMP"]) / "imports.json"
                    imports.write_text(json.dumps(gap.get("imports") or []))
                    guards = ["node", ".github/scripts/outside-guard.mjs", "imports",
                              str(target), str(imports), path, "check"]
                    good = run_check(guards, gid, stop)
                    if good:
                        good = run_check(
                            ["bash", "-c", 'cd lean && lake build "$1"', "check", "+" + module], gid, stop)
                    if good:
                        good = run_check(["node", "tools/check-lean.mjs", str(target),
                                          str(statement), "check"], gid, stop)
                    print("CANDIDATE_VERDICT", gid, digest, "ACCEPTED" if good else "NOT_ACCEPTED", flush=True)
                    target.unlink(missing_ok=True)
            stop.wait(15)
    finally:
        stop.set()
        thread.join(timeout=2)
        if not released:
            try:
                lease_action("release", lease, "out_of_time")
                print("RELEASED", gid, "out_of_time", flush=True)
            except Exception:
                print("LEASE_RELEASE_FAILED", gid, flush=True)
    if not released:
        break
