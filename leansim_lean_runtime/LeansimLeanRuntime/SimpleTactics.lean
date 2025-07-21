import Lean
import Batteries.Tactic.Exact
import Mathlib.Tactic.Basic

open Lean Elab Meta Parser Tactic

/-- factor out by definition of a local declaration off the target -/
syntax (name := unpack) &"unpack " (colGt ident)+ (location)? : tactic

/-- same as `unpack` except that it skips any candidate by which rewriting fails -/
syntax (name := unpack?) &"unpack? " (colGt ident)+ (location)? : tactic

def unpackAtLocal (weak : Bool) (lvars : Array (Syntax × FVarId × Expr)) (tvar : FVarId) : TacticM Unit :=  withMainContext do
  for (lname, lvar, lval) in lvars do withMainContext do
    let tType ← tvar.getType
    let t ← kabstract tType lval
    if !t.hasLooseBVars && !weak then
      throwErrorAt lname "no occurence of `{lname}` found"
    else if !t.hasLooseBVars && weak then
      pure ()
    else
      let newType := t.instantiate1 (Expr.fvar lvar)
      let newGoal ← (← getMainGoal).replaceLocalDeclDefEq tvar newType -- let-declaration always defeq
      replaceMainGoal [newGoal]

def unpackAtTarget (weak : Bool) (lvars : Array (Syntax × FVarId × Expr)) : TacticM Unit :=  withMainContext do
  for (lname, lvar, lval) in lvars do withMainContext do
    let target ← getMainTarget
    let newTarget ← kabstract target lval
    if !newTarget.hasLooseBVars && !weak then
      throwErrorAt lname "no occurence of `{lname}` found"
    else if !newTarget.hasLooseBVars && weak then
      pure ()
    else
      let newTarget := newTarget.instantiate1 (.fvar lvar)
      let newMVarId ← (← getMainGoal).replaceTargetDefEq newTarget
      replaceMainGoal [newMVarId]

@[tactic unpack, tactic unpack?, incremental]
def evalUnpack : Tactic := fun stx => withMainContext do
  let (weak, ldecls, _) ← match stx with
    | `(tactic| unpack $ldecls* $[$loc?]?) => pure (false, ldecls, loc?)
    | `(tactic| unpack? $ldecls* $[$loc?]?) => pure (true, ldecls, loc?)
    | _ => throwUnsupportedSyntax
  let loc := expandOptLocation stx[2]
  let lvars ← ldecls.filterMapM fun x => elabTermForApply x (mayPostpone := false) <&> fun
    | .fvar fvarId => some (fvarId, x)
    | _            => none -- skips the non-local names, because we might remove the tautologies like `retro a := a`
  let lvars ←
    if weak then
      lvars.filterMapM fun (lvar, name) => do
        return (name, lvar, ·) <$> (← lvar.getValue?)
    else
      lvars.mapM fun (lvar, name) => do
        if let some val ← lvar.getValue? then
          return (name, lvar, val)
        else
          throwErrorAt name "{name} has no visible value"
  withLocation loc (unpackAtLocal weak lvars) (unpackAtTarget weak lvars)
    fun goal => goal.withContext do throwError "unpack failed:\n{goal}"

syntax (name := renameThe) &"rename_the " ident " => " ident : tactic

@[tactic renameThe, incremental]
def evalRenameThe : Tactic := fun stx => withMainContext do
  let `(tactic| rename_the $x => $y) := stx | throwUnsupportedSyntax
  let var ← getFVarId x
  let newMVarId ← (← getMainGoal).rename var y.getId
  replaceMainGoal [newMVarId]

syntax (name := clear?) "clear?" colGt ident : tactic

@[tactic clear?, incremental]
def evalClear? : Tactic := fun stx =>
  match stx with
  | `(tactic| clear? $name) => discard <| observing? do
    let fvarId ← getFVarId name
    withMainContext do
      let mvarId ← (← getMainGoal).clear fvarId
      replaceMainGoal [mvarId]
  | _ => throwUnsupportedSyntax

/-- re-intro a variable
```
retro with [a] b := b x
```

is equivalent to

```
letI b := b x
unpack a at b
unpack? b
```
-/
syntax (name := retro) &"retro " (" with " "[" ident,* "] ")? ident Term.optType " := " term : tactic

/-- `have` version of `retro`
-/
syntax (name := retro') &"retro' " (" with " "[" ident,* "] ")? ident Term.optType " := " term : tactic

macro_rules
  | `(tactic| retro with [] $var $[$type?]? := $val) => do
    `(tactic| focus
      letI $var $[$type?]? := $val
      unpack? $var
      )
  | `(tactic| retro with [$unpacks,*] $var $[$type?]? := $val) => do
    `(tactic| focus
      letI $var $[$type?]? := $val
      unpack $unpacks* at $var:ident
      unpack? $var
      )
  | `(tactic| retro $var $[$type?]? := $val) => do
    `(tactic| focus
      letI $var $[$type?]? := $val
      unpack? $var
      )
  | `(tactic| retro' with [] $var $[$type?]? := $val) => do
    if let some _ := val.raw.find? (fun s => match s with | .ident _ _ n .. => n == var.getId | _ => false) then
      let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
      `(tactic| focus
        have $newName $[$type?]? := $val
        unpack? $newName
        clear? $var
        rename_the $newName => $var
        )
    else
      `(tactic| focus
        have $var $[$type?]? := $val
        unpack? $var
        )
  | `(tactic| retro' with [$unpacks,*] $var $[$type?]? := $val) => do
    if let some _ := val.raw.find? (fun s => match s with | .ident _ _ n .. => n == var.getId | _ => false) then
      let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
      `(tactic| focus
        have $newName $[$type?]? := $val
        unpack $unpacks* at $newName:ident
        unpack? $newName
        clear? $var
        rename_the $newName => $var
        )
    else
      `(tactic| focus
        have $var $[$type?]? := $val
        unpack $unpacks* at $var:ident
        unpack? $var
        )
  | `(tactic| retro' $var $[$type?]? := $val) => do
    if let some _ := val.raw.find? (fun s => match s with | .ident _ _ n .. => n == var.getId | _ => false) then
      let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
      `(tactic| focus
        have $newName $[$type?]? := $val
        unpack? $newName
        clear? $var
        rename_the $newName => $var
        )
    else
      `(tactic| focus
        have $var $[$type?]? := $val
        unpack? $var
        )

-- macro_rules
--   | `(tactic| retro with [] $var $[$type?]? := $val) => do
--     let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
--     `(tactic| focus
--       letI $newName $[$type?]? := $val
--       unpack? $newName
--       clear? $var
--       rename_the $newName => $var
--       )
--   | `(tactic| retro with [$unpacks,*] $var $[$type?]? := $val) => do
--     let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
--     `(tactic| focus
--       letI $newName $[$type?]? := $val
--       unpack $unpacks* at $newName:ident
--       unpack? $newName
--       clear? $var
--       rename_the $newName => $var
--       )
--   | `(tactic| retro $var $[$type?]? := $val) => do
--     let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
--     `(tactic| focus
--       letI $newName $[$type?]? := $val
--       unpack? $newName
--       clear? $var
--       rename_the $newName => $var
--       )
--   | `(tactic| retro' with [] $var $[$type?]? := $val) => do
--     let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
--     `(tactic| focus
--       have $newName $[$type?]? := $val
--       unpack? $newName
--       clear? $var
--       rename_the $newName => $var
--       )
--   | `(tactic| retro' with [$unpacks,*] $var $[$type?]? := $val) => do
--     let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
--     `(tactic| focus
--       have $newName $[$type?]? := $val
--       unpack $unpacks* at $newName:ident
--       unpack? $newName
--       clear? $var
--       rename_the $newName => $var
--       )
--   | `(tactic| retro' $var $[$type?]? := $val) => do
--     let newName := mkIdent <| var.getId.appendAfter "retro_tmp"
--     `(tactic| focus
--       have $newName $[$type?]? := $val
--       unpack? $newName
--       clear? $var
--       rename_the $newName => $var
--       )

-- example : True := by
--   let f x := x + 1
--   have f_def' : ∀ x, f x = x + 1 := by sorry
--   have : f 2 = 3 := by
--     -- let f := f 2
--     -- unpack f
--     retro f := f 2 with []



/--
`Γ, x : X := V ⊢ M`
↔ `Γ ⊢ let x : X := V, M`
⇐ `Γ ⊢ ∀ x : X, M`
↔ `Γ,x : X ⊢ M`

`mkOpaque` removes all values of let-declarations in the current context, **preserving order of all variables**.
-/
syntax (name := mkOpauqe) "mkOpaque" : tactic

partial def mkOpaqueInOrder (exit : LocalDecl → Bool) : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let some fvar := LocalDecl.fvarId <$> lctx.findDeclRev? fun x => if x.hasValue && !(exit x) then some x else none
      | return
    let (newFVars, newGoal) ← (← getMainGoal).revertAfter fvar
    let names ← Array.toList <$> newFVars.mapM fun x => x.getUserName
    let newGoal ← newGoal.clearValue fvar
    let (_, newGoal) ← newGoal.introN names.length names
    replaceMainGoal [newGoal]
    mkOpaqueInOrder exit

@[tactic mkOpauqe, incremental]
partial def evalMkOpaque : Tactic := fun _ => mkOpaqueInOrder fun _ => false

syntax (name := haveOpaque) "have_opaque " ident (" : " term)? " := " term : tactic

macro_rules
| `(tactic| have_opaque $n $[: $t]? := by $tacs) =>
  `(tactic|
    have $n:ident $[: $t]? := by
      mkOpaque
      . $tacs
    )


-- example : True := by
--   let a := 1
--   let b : Fin a := ⟨0, by simp⟩
--   have c : Nat := 0
--   let d := 2
--   mkOpaque

elab "clear_value_ordered " hs:(ppSpace colGt term:max)+ : tactic => withMainContext do
  let fvarIds ← getFVarIds hs
  let fvarIds ← sortFVarIds fvarIds
  if fvarIds.isEmpty then
    return
  let first := fvarIds[0]!
  let idx ← LocalDecl.index <$> first.getDecl
  withMainContext do
    mkOpaqueInOrder (fun x => x.index < idx)

syntax "elim_exists_inner " Term.anonymousCtor " := " term : tactic
syntax "elim_exists " Term.anonymousCtor " := " term : tactic

macro_rules
| `(tactic| elim_exists_inner ⟨$x:ident, $y:ident⟩ := $val) =>
  `(tactic|
    focus
      letI $x:ident := $(mkIdent ``Exists.choose) $val
      have $y:ident := $(mkIdent ``Exists.choose_spec) $val
    )
| `(tactic| elim_exists_inner ⟨$x:ident, $tail,*⟩ := $val) =>
  `(tactic|
    focus
      letI $x:ident := $(mkIdent ``Exists.choose) $val
      elim_exists_inner ⟨$tail,*⟩ := $(mkIdent ``Exists.choose_spec) $val
    )
| `(tactic| elim_exists ⟨$pat:ident,*, $last:ident⟩ := $val) =>
  `(tactic|
    focus
      elim_exists_inner ⟨$pat,*, $last⟩ := $val
      unpack $pat* at $last:ident
      -- clear_value_ordered $pat*
    )


-- example := by
--   have t : ∃ (x : Nat), ∃ y, ∃ z, ∃ w, x + y = z + w := sorry
--   -- test_init ⟨a, b, c, d, e⟩ := t
--   elim_exists ⟨a, b, c, d⟩ := t
