"""Generate Challenge.lean by verbatim copy from the JM library.

Copies the module body (variable line, all definitions, helper lemmas) byte-for-byte
from JM/Defs.lean, so that Lean's variable auto-binding produces syntactically
identical declaration types. Only the comparator-selected theorem proof is
replaced with a `sorry` placeholder.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEOREMS = ["jehiel_moldovanu_impossibility"]


def statement_sorry(source: str, name: str) -> str:
    match = re.search(r"(?m)^theorem " + re.escape(name) + r"\b[\s\S]*?:=", source)
    assert match, f"Missing theorem statement: {name}"
    return match.group(0) + " by\n  sorry\n"


def render() -> str:
    src = (ROOT / "JM" / "Defs.lean").read_text()
    # Imports block: the public imports at the top of the library file
    # (without the leading `module` line, which the header already emits).
    imports = src[: src.index("@[expose] public section")]
    assert imports.startswith("module\n"), "unexpected library header"
    imports = imports[len("module\n"):].lstrip("\n")
    namespace = "namespace JM\n"
    start = src.index(namespace) + len(namespace)
    # Body block: everything from after `namespace JM` up to the comparator theorem.
    stop = src.index("theorem jehiel_moldovanu_impossibility", start)
    body = src[start:stop].rstrip() + "\n\n"
    sorry_thm = statement_sorry(src, "jehiel_moldovanu_impossibility")
    header = '''module

%s
/-!
Compact comparison surface for the finite Jehiel-Moldovanu impossibility instance.
All definitions below are genuine, with their exact library bodies, copied
verbatim (including the variable binders) so that declaration types match
the library syntactically.
Only the comparator-selected theorem proof is a deliberate statement hole.
The complete, mechanically checked proof is in the JM library imported by
Solution. The proof was developed with AI assistance and then independently
compiled, audited for placeholders and axioms, and comparator-checked; no
separate independent human review of the proof was performed.
The official comparator checks its exact contract.
-/

@[expose] public section

namespace JM

open scoped BigOperators NNReal

''' % imports
    # The library wraps the body in `noncomputable section ... end`, with the
    # section's `end` placed after the comparator theorem. Keep the
    # sorry-theorem inside the section (verbatim structure), then close it.
    return header + body + sorry_thm + "\nend\n\nend JM\n"


def main() -> None:
    (ROOT / "Challenge.lean").write_text(render())
    print("wrote Challenge.lean")


if __name__ == "__main__":
    main()
