import Lake
open Lake DSL

package possibleWorldsSemantics

@[default_target]
lean_lib Spec

@[default_target]
lean_lib Grounding

@[default_target]
lean_lib Modality

@[default_target]
lean_lib Situation

@[default_target]
lean_lib Tests where
  globs := #[.submodules `Tests]

@[default_target]
lean_lib Model where
  globs := #[.submodules `Model]
