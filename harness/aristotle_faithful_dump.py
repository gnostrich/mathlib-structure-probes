#!/usr/bin/env python3
"""
aristotle_faithful_dump.py — obtain the FAITHFUL Mathlib declaration-dependency
graph by running DumpDeps.lean inside Aristotle's built Mathlib v4.28.0 environment,
then download decl_deps.jsonl. This is the route used when the local Lean toolchain
+ Mathlib olean cache are egress-blocked (github releases / *.blob.core.windows.net),
which is what happened in the sessions that produced this kit.

Aristotle (Harmonic, https://aristotle.harmonic.fun) runs an agent on an uploaded
Lean project in a fully-built Mathlib env and returns the resulting files via
get_files(). We upload the certified-generator project (output-final_aristotle/,
which pins Mathlib v4.28.0 and does `import Mathlib`) plus DumpDeps.lean, instruct
the agent to compile+run it, and pull back decl_deps.jsonl.

Provenance of the run committed with this kit:
  - Aristotle expected toolchain == leanprover/lean4:v4.28.0 (matches the project).
  - Two independent jobs returned BYTE-IDENTICAL decl_deps.jsonl
    (md5 9f3a3c364cf975525e50049d10df194c), 333,044 declarations, 7,523,067 internal
    edges, avg 28.7 value-deps / 16.7 type-deps per decl (proof-synthesized edges
    present, unlike the statement-only approx graph).

Usage:
  export ARISTOTLE_API_KEY=...            # your key (not cost-metered on this plan)
  python harness/aristotle_faithful_dump.py /path/to/output-final_aristotle /path/to/DumpDeps.lean out_dir
Then:
  python harness/loop_veto_test.py out_dir/decl_deps.jsonl     # the faithful decisive run

Requires: pip install aristotlelib
"""
import os, sys, asyncio, tarfile, shutil, tempfile, pathlib
import aristotlelib as A

SCHEMA = ('{"name": <fq name>, "module": <module>, "kind": "theorem"|"def"|"axiom"|"other", '
          '"type_deps": [<constants used in the TYPE>], "value_deps": [<constants used in the VALUE/proof term>]}')

PROMPT = (
 "This is a Lean 4 project pinned to leanprover/lean4:v4.28.0 depending on Mathlib v4.28.0; it already "
 "does `import Mathlib`. THIS IS NOT A THEOREM-PROVING TASK. Make `RequestProject/DumpDeps.lean` COMPILE "
 "and RUN on this toolchain so it writes `decl_deps.jsonl` in the PROJECT ROOT: one JSON object per line, "
 "one line per non-internal declaration whose module is under `Mathlib`, EXACT schema:\n" + SCHEMA + "\n"
 "type_deps/value_deps must be FAITHFUL kernel references (Lean.Expr.getUsedConstants on the type and on "
 "the value), which include proof-synthesized constants. Fix any v4.28.0 API drift minimally but keep the "
 "schema and one-line-per-decl behavior. Build the full `import Mathlib`. When done, verify decl_deps.jsonl "
 "exists with ~100k-250k+ lines, LEAVE it in place, and report the exact line count. If a run_cmd write is "
 "not permitted, instead add a `lean_exe` with `main : IO Unit` that materializes the env and writes the "
 "file. Do not modify the other RequestProject/*.lean math files.")

async def main(project_dir, dumpdeps_lean, out_dir, n_parallel=2):
    A.set_api_key(os.environ["ARISTOTLE_API_KEY"])
    out_dir = pathlib.Path(out_dir); out_dir.mkdir(parents=True, exist_ok=True)

    # stage upload = project_dir + DumpDeps.lean placed under RequestProject/
    with tempfile.TemporaryDirectory() as tmp:
        stage = pathlib.Path(tmp) / "proj"
        shutil.copytree(project_dir, stage)
        shutil.rmtree(stage / ".lake", ignore_errors=True)
        shutil.rmtree(stage / ".git", ignore_errors=True)
        shutil.copy(dumpdeps_lean, stage / "RequestProject" / "DumpDeps.lean")

        # launch N redundant jobs concurrently (Aristotle is slow; redundancy hedges failure)
        projs = await asyncio.gather(*[
            A.Project.create_from_directory(prompt=PROMPT, project_dir=str(stage),
                                            agent_questions_setting=A.AgentQuestionsSetting.DISABLED)
            for _ in range(n_parallel)])
        pids = [p.model_dump().get("project_id") for p in projs]
        print("launched project_ids:", pids, flush=True)

        # poll until one goes IDLE with files, then download + extract decl_deps.jsonl
        while True:
            await asyncio.sleep(60)
            for pid in pids:
                p = await A.Project.from_id(pid)
                d = p.model_dump()
                print(f"  {pid}: status={d.get('status')} has_files={d.get('has_files')}", flush=True)
                if d.get("status") == 2 and d.get("has_files"):
                    tarpath = out_dir / f"{pid}.tar.gz"
                    await p.get_files(destination=str(tarpath))
                    with tarfile.open(tarpath, "r:*") as t:
                        for m in t.getmembers():
                            if os.path.basename(m.name) == "decl_deps.jsonl":
                                m.name = "decl_deps.jsonl"
                                t.extract(m, out_dir)
                                fp = out_dir / "decl_deps.jsonl"
                                n = sum(1 for _ in open(fp, "rb"))
                                print(f"SUCCESS: {fp} ({n} lines)", flush=True)
                                return
        # (add a max-iteration bound in production)

if __name__ == "__main__":
    pd, dd, od = sys.argv[1], sys.argv[2], sys.argv[3]
    asyncio.run(main(pd, dd, od))
