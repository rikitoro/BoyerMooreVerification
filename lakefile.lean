import Lake
open Lake DSL

package "BoyerMooreVerification" where
  version := v!"0.1.0"

lean_lib BMModel

lean_lib BMChallenge

@[default_target]
lean_lib BMProofs
