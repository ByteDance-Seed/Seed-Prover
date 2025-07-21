-- Copyright (c) 2024 Bytedance Ltd. and/or its affiliates
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

import Lean
import Mathlib
import Qq
open Classical

namespace Leansim.Tactic

lemma inh_card {a b : Finset α} : a = b → a.card = b.card := congrArg _
lemma inh_length {a b : List α} : a = b → a.length = b.length := congrArg _
lemma powerset_finset {a b : Finset α} : a = b → a.powerset = b.powerset := congrArg _

end Leansim.Tactic

section

open Lean Meta Parser Term PrettyPrinter Delaborator SubExpr
open TSyntax.Compat

@[delab app.OfNat.ofNat]
def delabOfNat : Delab := withOverApp 3 do
  delabOfNatCore (showType := (← getPPOption getPPNumericTypes))

@[delab app.Exists]
def delabExists : Delab := whenPPOption Lean.getPPNotation do
  let #[_, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      `(∃ ($x:ident : $dom), $body)

private partial def delabForallBinders (delabGroup : Array Syntax → Bool → Syntax → Delab) (curNames : Array Syntax := #[]) (curDep := false) : Delab := do
  let dep := !(← getExpr).isArrow
  if !curNames.isEmpty && dep != curDep then
    delabGroup curNames curDep (← delab)
  else
    let curDep := dep
    let (stx, stxN) ← withBindingBodyUnusedName fun stxN => return (← delab, stxN)
    delabGroup (curNames.push stxN) curDep stx

@[delab forallE]
def delabForall : Delab := do
  delabForallBinders fun curNames dependent stxBody => do
    let e ← getExpr
    let prop ← try Meta.isProp e catch _ => pure false
    let stxT ← withBindingDomain delab
    let group ← match e.binderInfo with
    | BinderInfo.implicit       => `(bracketedBinderF|{$curNames* : $stxT})
    | BinderInfo.strictImplicit => `(bracketedBinderF|⦃$curNames* : $stxT⦄)
    | BinderInfo.instImplicit   => `(bracketedBinderF|[$curNames.back : $stxT])
    | _                         =>
      if dependent then
        if prop && !(← getPPOption getPPPiBinderTypes) then
          return ← `(∀ $curNames:ident*, $stxBody)
        else
          `(bracketedBinderF|($curNames* : $stxT))
      else
        return ← curNames.foldrM (fun _ stxBody => `($stxT → $stxBody)) stxBody
    if prop then
      `(∀ $group, $stxBody)
    else
      `($group:bracketedBinder → $stxBody)

@[delab app.Subtype.mk]
def delabSubtypeMk : Delab := withOverApp 4 do
  let #[α, p, val, proof] := (← getExpr).getAppArgs | failure
  let valTerm ← withNaryArg 2 delab
  let proofTerm ← withNaryArg 3 delab
  let typeTerm ← withType delab
  `((⟨ $valTerm, $proofTerm ⟩ : $typeTerm))

@[delab app.Subtype]
def delabSubtypeSetLike : Delab := do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  -- TODO: enough for `Set`/`Finset`/`List`?
  let S ← withAppArg <| withBindingBody n <| withNaryArg 4 delab
  `(↥$S)

@[delab app]
def coeDelaborator : Delab := do
  let e ← getExpr
  guard <| ← isTypeCorrect e
  guard <| ← isType e
  let .const declName _ := e.getAppFn | failure
  let some info ← Meta.getCoeFnInfo? declName | failure
  withOverApp info.numArgs do
    `(↥$(← withNaryArg info.coercee delab))

@[delab lam]
def delabLam : Delab := do
  let e ← getExpr
  let eta ← lambdaTelescope e fun xs body => do
    let t ← xs.anyM fun x => do
      let bi ← x.fvarId!.getBinderInfo
      return !bi.isExplicit
    if t then
      return false
    let args := body.getAppArgs
    return args == xs
  guard eta
  delab e.eta

@[delab app.List.nil]
def delabListNil : Delab := withOverApp 1 do
  let e ← getExpr
  let type ← inferType e
  let type ← instantiateMVars type
  guard !type.hasMVar
  let type ← withType delab
  `(([] : $type))

@[delab app.Bot.bot]
def delabBot : Delab := withOverApp 2 do
  let e ← getExpr
  let type ← inferType e
  let type ← instantiateMVars type
  guard !type.hasMVar
  let type ← withType delab
  `((⊥ : $type))

@[delab app.Top.top]
def delabTop : Delab := withOverApp 2 do
  let e ← getExpr
  let type ← inferType e
  let type ← instantiateMVars type
  guard !type.hasMVar
  let type ← withType delab
  `((⊤ : $type))

@[delab app.Nat.cast, delab app.Int.cast, delab app.Rat.cast, delab app.Real.cast]
def delabNatCast : Delab := withOverApp 3 do
  let e ← getExpr
  let type ← inferType e
  let type ← instantiateMVars type
  guard !type.hasMVar
  let val ← withAppArg delab
  let type ← withType delab
  `((↑($val) : $type))

@[delab app.Real.pi]
def delabRealPi: Delab := do
  `($(mkIdent ``Real.pi))

@[delab app.Singleton.singleton]
private def delabSingleton_singleton : Delab := withOverApp 4 do
  let s ← withNaryArg 1 delab
  let r ← withNaryArg 3 delab
  let a ← `(«term{_}»| {$r})
  `(($a : $s))

@[delab app.Insert.insert]
private partial def delabInsert_insert : Delab := withOverApp 5 do
  let s ← withNaryArg 1 delab
  let xs ← helper
  let xs := xs.toArray
  let a ← `(«term{_}»| {$xs,*})
  `(($a : $s))
where helper : DelabM (List Term) := do
    let e ← getExpr
    if e.isAppOfArity ``Singleton.singleton 4 then
      let s ← withNaryArg 3 delab
      return [s]
    if not <| e.isAppOfArity ``Insert.insert 5 then
      failure
    let x ← withNaryArg 3 delab
    let xs ← withNaryArg 4 helper
    return x :: xs

end

section

open Lean Parser Elab Meta Command Tactic Qq

def syntax_override_body_value : Parser :=
  withAntiquot (mkAntiquot "syntax_override_body_value" `syntax_override_body_value) (" := " >> Term.app)

syntax syntax_override_body_by := " by " stx+
syntax syntax_override_body_eq := " := " term
syntax syntax_override_body := syntax_override_body_by <|> syntax_override_body_eq

-- @[command_parser]
-- def syntax_override_parser : Parser := leading_parser "syntax_override " >> ident >> syntax_override_body

syntax (name := syntaxOverride) "syntax_override " ident syntax_override_body : command
open TSyntax.Compat in
set_option hygiene false in
@[command_elab syntaxOverride] def elabSyntaxOverride : Command.CommandElab := fun stx => do
  let (declName, val) ← Command.runTermElabM fun _ =>
    match stx with
    | `(command| syntax_override $declName:ident by $[$ps]*) => do
      let body ← Prod.fst <$> Term.toParserDescr (mkNullNode ps) Name.anonymous
      pure (declName, body)
    | `(command| syntax_override $declName:ident := $body) =>
      pure (declName, body)
    | _ => throwUnsupportedSyntax
  let oldNodeKind := declName.getId
  let some ci := (← getEnv).find? oldNodeKind | throwErrorAt declName "no such declaration found"
  let some dv := ci.value? | throwErrorAt declName "the specified declaration has no visible value"
  let parserDescrType := Expr.const ``ParserDescr []
  let oldDescr ← Command.runTermElabM fun _ => unsafe evalExpr ParserDescr parserDescrType dv
  let stxNodeKind := declName.getId.append `override
  let stxFmt := declName.getId.append `override.formatter
  let mkRoot : Name → Name := fun s =>
    let p := `_root_
    if p.isPrefixOf s then s
    else p.append s
  let newDescr ←
    match oldDescr with
    | .nodeWithAntiquot name kind _ =>
      `(def $(mkIdent (mkRoot stxNodeKind)):ident : Lean.ParserDescr := ParserDescr.nodeWithAntiquot $(quote name):term $(quote kind):term $val)
    | .node kind prec _ =>
      `(def $(mkIdent (mkRoot stxNodeKind)):ident : Lean.ParserDescr := ParserDescr.node $(quote kind):term $(quote prec):num $val)
    | _ => throwErrorAt declName "the specified declaration has wrong shape"
  let fmtCommand ← `(command|
    @[formatter $declName]
    def $(mkIdent (mkRoot stxFmt)):ident : Lean.PrettyPrinter.Formatter := Lean.PrettyPrinter.Formatter.formatterForKind $(quote stxNodeKind))
  let cmds := mkNullNode #[newDescr, fmtCommand]
  -- Command.runTermElabM fun _ => do
  --   println! "{← PrettyPrinter.ppCommand newDescr}"
  --   println! "{← PrettyPrinter.ppCommand fmtCommand}"
  Command.withMacroExpansion stx cmds <| Command.elabCommand cmds

open PrettyPrinter.Delaborator SubExpr in
section

@[local delab app.Lean.Name.mkStr1]
def delabMkStr1 : PrettyPrinter.Delaborator.Delab := withOverApp 1 do
  let t ← withNaryArg 0 delab
  let n := mkIdent ``Lean.Name.mkStr1
  `($n $t)

@[local delab app.Lean.Name.mkStr2]
def delabMkStr2 : PrettyPrinter.Delaborator.Delab := withOverApp 2 do
  let t ← withNaryArg 0 delab
  let s ← withNaryArg 1 delab
  let n := mkIdent ``Lean.Name.mkStr2
  `($n $t $s)

@[local delab app.Lean.Name.mkStr3]
def delabMkStr3 : PrettyPrinter.Delaborator.Delab := withOverApp 3 do
  let t ← withAppFn delab
  let s ← withAppArg delab
  `($t $s)

@[local delab app.Lean.Name.mkStr4]
def delabMkStr4 : PrettyPrinter.Delaborator.Delab := withOverApp 4 do
  let t ← withAppFn delab
  let s ← withAppArg delab
  `($t $s)

@[local delab app.Lean.Name.mkStr5]
def delabMkStr5 : PrettyPrinter.Delaborator.Delab := withOverApp 5 do
  let t ← withAppFn delab
  let s ← withAppArg delab
  `($t $s)

@[local delab app.Lean.Name.mkStr6]
def delabMkStr6 : PrettyPrinter.Delaborator.Delab := withOverApp 6 do
  let t ← withAppFn delab
  let s ← withAppArg delab
  `($t $s)

@[local delab app.Lean.Name.mkStr7]
def delabMkStr7 : PrettyPrinter.Delaborator.Delab := withOverApp 7 do
  let t ← withAppFn delab
  let s ← withAppArg delab
  `($t $s)

@[local delab app.Lean.Name.mkStr8]
def delabMkStr8 : PrettyPrinter.Delaborator.Delab := withOverApp 8 do
  let t ← withAppFn delab
  let s ← withAppArg delab
  `($t $s)

syntax_override Lean.Parser.Tactic.location by withPosition(ppGroup(" at" (locationWildcard <|> locationHyp)))

/- this `#eval` finds all `ParserDescr` referencing `location` and override them with `location.override` -/
#eval do
  let env ← getEnv (m := CommandElabM)
  let cs := env.constants.map₁
  for (cName, cInfo) in cs do
    if (`_cstage1).isSuffixOf cName then
      continue
    if cInfo.type != q(ParserDescr) then
      continue
    let some v := cInfo.value? | continue
    if !(v.getUsedConstantsAsSet.contains ``Lean.Parser.Tactic.location) then
      continue
    let some (_, _, v) := v.app3? ``ParserDescr.node <|> v.app3? ``ParserDescr.nodeWithAntiquot
      | throwError "cannot proceed"
    let name := (`_root_).isPrefixOf? cName |>.getD cName
    let v := v.replace fun e =>
      if e.isConstOf ``Lean.Parser.Tactic.location then
        some (Expr.const ``Lean.Parser.Tactic.location.override [])
      else none
    let val ← Command.runTermElabM fun _ => PrettyPrinter.delab v
    let s ← `(command| syntax_override $(mkIdent name) := $val)
    elabCommand s
    -- let x ← MonadLog.hasErrors
    -- if x then
    --   println! "{s}"
    --   println! "{cName}"
    --   break
end

end

theorem Or.elim_left {a b c : Prop} (h : a ∨ b → c) : a → c := fun x => h (Or.inl x)

theorem Or.elim_right {a b c : Prop} (h : a ∨ b → c) : b → c := fun x => h (Or.inr x)

theorem Subtype.val_eq_of_eq {p : α → Prop} {a1 a2 : α} {p1 : p a1} {p2 : p a2} : (⟨a1, p1⟩ : {x // p x}) = ⟨a2, p2⟩ → a1 = a2 :=
  Subtype.ext_iff_val.mp

theorem Function.Injective.mk {f : α → β} : (∀ (x y : α), f x = f y → x = y) → Function.Injective f := fun h x y => h x y

theorem if_elim_pos {α : Sort u} {h : Prop} {a b : α} (p : h) : (if h then a else b) = a := by
  simp [p]

theorem if_elim_neg {α : Sort u} {h : Prop} {a b : α} (p : ¬ h) : (if h then a else b) = b := by
  simp [p]

theorem em_elim {h : Prop} {α : Prop} (hp : h → α) (hn : ¬h → α) : α := by
  apply dite h hp hn

def Multiset.card' : Multiset α → ℕ := DFunLike.coe Multiset.card

@[simp]
theorem Multiset.card'_def {a : Multiset α} : Multiset.card' a = Multiset.card a := by simp [Multiset.card']


open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.DFunLike.coe]
private def delabDFunLike_coe : Delab := withOverApp 6 do
  let f ← withNaryArg 4 delab
  let x ← withNaryArg 5 delab
  `($f $x)


namespace ComplexConjugate

open Lean PrettyPrinter Delaborator SubExpr
@[scoped delab app.DFunLike.coe]
private def delabCoe_starRingEnd : Delab := withOverApp 6 do
  withNaryArg 4 do
    let e ← getExpr
    if e.isAppOfArity ``starRingEnd 3 then
      pure ()
    else failure
  let x ← withNaryArg 5 delab
  `(conj $x)

end ComplexConjugate
