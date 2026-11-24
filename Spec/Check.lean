import Lean

/-
  CHECKING THAT EVERY AXIOM IS A FIELD

  `#check_axioms_are_fields` is run in Tests/Specification.lean, after
  every library of the development has been imported.  It is kept
  apart from the development so that only the test imports `Lean`.
-/

open Lean Elab Command in
/-- Fails unless the axioms declared in Grounding/, Modality/ and
    Situation/ are exactly the fields of `Spec.Theory`, each field of
    `developmentTheory` is the axiom of its name, and every source file
    of those libraries is imported. -/
elab "#check_axioms_are_fields" : command => do
  let env ← getEnv
  let libs : List Name := [`Grounding, `Modality, `Situation]
  let inLibs (m : Name) : Bool := libs.any (·.isPrefixOf m)
  -- every source file is imported
  let mut problems : Array String := #[]
  for lib in libs do
    let files ← liftM (m := IO) <| System.FilePath.walkDir lib.toString
    for f in files do
      if f.extension == some "lean" then
        let parts := (f.withExtension "").components
        let mod := parts.foldl (fun n s => Name.str n s) Name.anonymous
        unless env.header.moduleNames.contains mod do
          problems := problems.push s!"module {mod} is not imported"
  -- the axioms of the development
  let mut axs : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .axiomInfo _ := ci then
      if let some idx := env.getModuleIdxFor? n then
        if inLibs env.header.moduleNames[idx.toNat]! then
          axs := axs.push n
  let fields := (getStructureFields env `Spec.Theory).toList
  for a in axs do
    unless fields.contains a do
      problems := problems.push s!"axiom {a} is not a field of Spec.Theory"
  -- every field of developmentTheory is the axiom of its name
  let some (.defnInfo d) := env.find? `developmentTheory
    | throwError "developmentTheory not found"
  let args := d.value.getAppArgs.toList
  unless args.length == fields.length do
    problems := problems.push "developmentTheory has the wrong number of fields"
  for (fld, arg) in fields.zip args do
    match arg with
    | .const c _ =>
      unless c == fld && axs.contains c do
        problems := problems.push s!"field {fld} is filled by {c}, not by the axiom {fld}"
    | _ => problems := problems.push s!"field {fld} is not filled by an axiom"
  unless problems.isEmpty do
    throwError "axiom check failed:\n{String.intercalate "\n" problems.toList}"
  logInfo m!"axiom check passed: {axs.size} axioms, each a field of Spec.Theory, \
    filled by itself in developmentTheory"

open Lean Elab Command in
/-- Fails unless the named constant depends on no axioms beyond Lean's
    own: `propext`, `Classical.choice` and `Quot.sound`.  In particular
    it fails if the constant depends on `sorryAx` or on an axiom of the
    development. -/
elab "#check_only_core_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let axs ← liftCoreM <| collectAxioms n
  let core : List Name := [`propext, `Classical.choice, `Quot.sound]
  let extra := axs.toList.filter (fun a => !core.contains a)
  unless extra.isEmpty do
    throwError "{n} depends on axioms beyond Lean's own: {extra}"
  logInfo m!"{n} depends only on Lean's own axioms: {axs.toList}"
