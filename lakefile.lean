/-
Modified from openai/math (adc7f1241), file `lean/lakefile.lean`, by Jeroen Zuiddam, 2026:
reduced to the two dependencies this project imports (Mathlib and fixed-point-theorems, at the
same pinned commits as upstream) and to the one compatibility patch they need
(`patches/fixed-point-theorems-lean4341.patch`, copied verbatim from upstream), applied by the
`post_update` hook below, which is upstream's hook restricted to that one dependency.
-/
import Lake

open System Lake DSL

package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require «fixed-point-theorems» from git
  "https://github.com/harfe/fixed-point-theorems-lean4.git" @ "770940ddf9878cf61952ed53d910b92bca841838"

-- Declare shared dependencies last: Lake resolves later requirements first.
-- This pin overrides the older Mathlib in fixed-point-theorems' manifest.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib OAI

lean_lib ComparatorChallenges where globs := #[`ComparatorChallenges.+]

private def patchGit (directory : FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args := #["-C", directory.toString] ++ args }

private def checkPatch (directory patch : FilePath) (args : Array String := #[]) :
    IO IO.Process.Output :=
  patchGit directory (#["apply", "--check"] ++ args ++ #[patch.toString])

post_update pkg do
  -- Preflight every dependency before changing any of them.
  let mut plans := #[]
  for name in #[`«fixed-point-theorems»] do
    let label := name.toString (escape := false)
    let some dep ← findPackageByName? name
      | error s!"Missing dependency {label}; run lake update from the project root."
    let some declaration := pkg.depConfigs.find? (·.name == name)
      | error s!"Missing direct dependency declaration for {label}."
    let some (.git _ (some revision) _) := declaration.src?
      | error s!"{label} must be pinned to a Git commit."
    let patchDirectory := dep.dir
    let head ← patchGit patchDirectory #["rev-parse", "HEAD"]
    unless head.exitCode == 0 && head.stdout.trimAscii.toString == revision do
      error s!"{label}: expected commit {revision}, got {head.stdout}\n{head.stderr}"
    let patchNames := #[s!"{label}-lean4341.patch"]
    for patchName in patchNames do
      let patch := pkg.dir / "patches" / FilePath.mk patchName
      unless ← patch.pathExists do
        error s!"Missing compatibility patch: {patch}"
      let reverse ← checkPatch patchDirectory patch #["--reverse"]
      if reverse.exitCode == 0 then
        plans := plans.push (label, patchDirectory, patch, none)
        continue
      let forward ← checkPatch patchDirectory patch
      if forward.exitCode == 0 then
        plans := plans.push (label, patchDirectory, patch, some patch)
        continue
      error s!"{label}: compatibility patch {patch} conflicts with local changes.\n\
        Forward check:\n{forward.stderr}\nReverse check:\n{reverse.stderr}"
  for (label, directory, patch, action) in plans do
    let patchName := patch.fileName.getD patch.toString
    if let some toApply := action then
      let result ← patchGit directory #["apply", toApply.toString]
      unless result.exitCode == 0 do
        error s!"{label}: failed to apply {toApply}:\n{result.stderr}"
      let verified ← checkPatch directory patch #["--reverse"]
      unless verified.exitCode == 0 do
        error s!"{label}: patch verification failed:\n{verified.stderr}"
      logInfo s!"{label}: applied compatibility patch {patchName}"
    else
      logInfo s!"{label}: compatibility patch already applied: {patchName}"
