import Lean
open Lean Lean.Elab Lean.Elab.Tactic Lean.Parser.Tactic

-- Allow a single `rewrite` without brackets
macro (name := rewriteOne) (priority := low)
  "rewrite" rule:rwRule loc?:(location)? : tactic =>
  match loc? with
  | none => `(tactic| rewrite [$rule])
  | some loc => `(tactic| rewrite [$rule] $loc)

-- Allow a single `rw` without brackets
macro (name := rwOne) (priority := low)
  "rw" rule:rwRule loc?:(location)? : tactic =>
  match loc? with
  | none => `(tactic| rw [$rule])
  | some loc => `(tactic| rw [$rule] $loc)

-- Allow a single `dsimp` without brackets (couldn't get this one to work as a
-- macro)
syntax (name := dsimpOne) (priority := low)
  "dsimp" (&" only")? (simpErase <|> simpLemma) (location)? : tactic

@[tactic dsimpOne] def evalDSimpOne : Tactic := λ stx => do
  let realStx ←
    match stx with
    | `(dsimpOne| dsimp $lem) =>
      `(tactic| dsimp [$lem])
    | `(dsimpOne| dsimp only $lem) =>
      `(tactic| dsimp only [$lem])
    | `(dsimpOne| dsimp $lem $loc) =>
      `(tactic| dsimp [$lem] $loc)
    | `(dsimpOne| dsimp only $lem $loc) =>
      `(tactic| dsimp only [$lem] $loc)
    | _ => throwUnsupportedSyntax
  evalDSimp realStx
