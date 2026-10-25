#!/usr/bin/env python3
"""Regression checks for module ownership and fail-closed axiom auditing.

Fixtures live only in a temporary .lake directory and are removed on exit. The
negative fixture deliberately depends on an unapproved synthetic axiom; it must
be rejected by the audit even though that axiom belongs to another module.
"""

from pathlib import Path
import os
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1] / "rudin"


def main():
    subprocess.run(["lake", "build", "Rudin.PMA.AxiomAudit"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="axiom-audit-", dir=ROOT / ".lake") as raw:
        scratch = Path(raw)
        env = dict(os.environ)
        env["LEAN_PATH"] = str(scratch) + os.pathsep + env.get("LEAN_PATH", "")

        def lean(module, source, *, compile_module=False, expected_error=None):
            path = scratch.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            command = ["lake", "env", "lean", "--root", str(scratch), str(path)]
            if compile_module:
                command += ["-o", str(path.with_suffix(".olean"))]
            result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if expected_error is None:
                if result.returncode:
                    raise RuntimeError(f"{module} failed:\n{result.stdout}")
            elif result.returncode == 0 or expected_error not in result.stdout:
                raise RuntimeError(f"{module} did not reject as expected:\n{result.stdout}")
            return result.stdout

        lean("AuditFixture.Generated", """import Rudin.PMA.AxiomAudit
namespace OutsideNamespace
inductive Marker where | item
def step : Nat → Nat | 0 => 0 | n + 1 => n
theorem step_zero : step 0 = 0 := step.eq_1
private theorem hidden : True := True.intro
end OutsideNamespace
""", compile_module=True)
        lean("AuditFixture", """import AuditFixture.Generated
theorem AnotherNamespace.root : True := True.intro
""", compile_module=True)
        output = lean("PositiveAudit", """import AuditFixture
run_cmd do
  let env ← Lean.getEnv
  let hidden := env.constants.fold (init := #[]) fun names name _ =>
    if Lean.privateToUserName name == `OutsideNamespace.hidden then names.push name else names
  if hidden.size != 1 then throwError "Expected exactly one private fixture theorem."
  Rudin.PMA.Audit.checkModuleAxioms `AuditFixture
    (#[`OutsideNamespace.step.eq_1, `OutsideNamespace.Marker.item, `AnotherNamespace.root] ++ hidden)
""")
        for expected in ["Axiom audit module AuditFixture.Generated:",
                         "OutsideNamespace.step.eq_1", "OutsideNamespace.hidden",
                         "no forbidden axioms"]:
            if expected not in output:
                raise RuntimeError(f"Missing positive coverage {expected}:\n{output}")
        lean("CurrentAudit", """import Rudin.PMA.AxiomAudit
private theorem Elsewhere.current : True := True.intro
run_cmd Rudin.PMA.Audit.checkModuleAxioms `CurrentAudit
""")
        lean("MissingAudit", """import Rudin.PMA.AxiomAudit
run_cmd Rudin.PMA.Audit.checkModuleAxioms `NotImported
""", expected_error="is not imported or current")
        lean("EmptyFixture", "import Rudin.PMA.AxiomAudit\n", compile_module=True)
        lean("EmptyAudit", """import EmptyFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `EmptyFixture
""", expected_error="found no declarations")
        lean("EmptyAuditAllowed", """import EmptyFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `EmptyFixture (allowEmpty := true)
""")
        lean("CoverageAudit", """import AuditFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `AuditFixture #[`Missing.declaration]
""", expected_error="coverage regression")
        lean("UnapprovedDependency", """import Rudin.PMA.AxiomAudit
axiom Unrelated.unapproved : False
""", compile_module=True)
        lean("NegativeFixture", """import UnapprovedDependency
theorem OutsideNamespace.bad : False := Unrelated.unapproved
""", compile_module=True)
        lean("NegativeAudit", """import NegativeFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `NegativeFixture
""", expected_error="Forbidden axioms in OutsideNamespace.bad")
    print("Axiom-audit regression checks passed: imported/generated/private/current "
          "declarations, submodules, missing/empty modules, required coverage, and "
          "transitive forbidden-axiom rejection.")


if __name__ == "__main__":
    main()
