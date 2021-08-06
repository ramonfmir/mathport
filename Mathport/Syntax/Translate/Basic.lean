/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Bridge.Path
import Mathport.Syntax.Data4
import Mathport.Syntax.Translate.Notation
import Mathport.Syntax.Translate.Attributes
import Mathport.Syntax.Translate.Parser

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open Lean.Elab (Visibility)
open Lean.Elab.Command (CommandElabM liftCoreM)

namespace Translate

open Std (HashMap)
open AST3

structure Scope where
  curNamespace : Name := Name.anonymous
  oldStructureCmd : Bool := false
  deriving Inhabited

structure NotationData where
  n3 : String
  n4 : Name
  desc : NotationDesc

def NotationData.unpack : NotationData → NotationEntry
  | ⟨n3, n4, NotationDesc.builtin⟩ => (predefinedNotations.find? n3).get!
  | ⟨n3, n4, desc⟩ => ⟨n4, desc, desc.toKind n4, false⟩

abbrev NotationEntries := HashMap String NotationData

structure State where
  output : Format := ""
  current : Scope := {}
  scopes : Array Scope := #[]
  simpSets : NameSet := predefinedSimpSets
  tactics : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax) := {}
  userNota : NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax) := {}
  deriving Inhabited

def NotationEntries.insert (m : NotationEntries) : NotationData → NotationEntries
  | d => HashMap.insert m d.n3 d

initialize synportNotationExtension : SimplePersistentEnvExtension NotationData NotationEntries ←
  registerSimplePersistentEnvExtension {
    name          := `Mathport.Translate.synportNotationExtension
    addEntryFn    := NotationEntries.insert
    addImportedFn := fun es => mkStateFromImportedEntries NotationEntries.insert {} es
  }

def getNotationEntry? (s : String) : CommandElabM (Option NotationEntry) := do
  match synportNotationExtension.getState (← getEnv) |>.find? s with
  | none => predefinedNotations.find? s
  | some d => d.unpack

def registerNotationEntry (d : NotationData) : CommandElabM Unit := do
  modifyEnv fun env => synportNotationExtension.addEntry env d

structure Context where
  pcfg : Path.Config
  notations : Array Notation
  commands : Array Command
  trExpr : Expr → CommandElabM Syntax
  trCommand : Command → CommandElabM Unit
  deriving Inhabited

abbrev M := ReaderT Context $ StateRefT State CommandElabM

def trExpr (e : Expr) : M Syntax := do (← read).trExpr e
def trCommand (e : Command) : M Unit := do (← read).trCommand e

def renameIdent (n : Name) : M Name := do Rename.resolveIdent! (← getEnv) n
def renameNamespace (n : Name) : M Name := do Rename.renameNamespace (← getEnv) n
def renameAttr (n : Name) : M Name := do Rename.renameAttr n
def renameModule (n : Name) : M Name := do Rename.renameModule (← read).pcfg n
def renameField (n : Name) : M Name := do Rename.renameField? (← getEnv) n |>.getD n
def renameOption : Name → M Name
  | n => do dbg_trace "unsupported option {n}"; n

def mkIdentI (n : Name) : M Syntax := do mkIdent (← renameIdent n)
def mkIdentA (n : Name) : M Syntax := do mkIdent (← renameAttr n)
def mkIdentN (n : Name) : M Syntax := do mkIdent (← renameNamespace n)
def mkIdentF (n : Name) : M Syntax := do mkIdent (← renameField n)
def mkIdentO (n : Name) : M Syntax := do mkIdent (← renameOption n)

def AST3toData4 : AST3 → M Data4
  | ⟨prel, imp, commands, _, _⟩ => do
    let prel := prel.map fun _ => mkNode ``Parser.Module.prelude #[mkAtom "prelude"]
    let imp ← imp.foldlM (init := #[]) fun imp ns =>
      ns.foldlM (init := imp) fun imp n => do
        imp.push $ mkNode ``Parser.Module.import #[mkAtom "import",
          mkNullNode, mkIdent (← renameModule n.kind)]
    let fmt ← liftCoreM $ PrettyPrinter.format Parser.Module.header.formatter $
      mkNode ``Parser.Module.header #[mkOptionalNode prel, mkNullNode imp]
    modify fun s => { s with output := fmt }
    commands.forM fun c => do
      try trCommand c.kind
      catch e =>
        let e := s!"error in {(← getEnv).mainModule}: {← e.toMessageData.toString}"
        println! e
        -- println! (repr c.kind)
        modify fun s => { s with
          output := s.output ++ "-- " ++ e ++ "\n" ++ (repr c.kind).group ++ "\n\n" }
    let s ← get
    pure ⟨s.output, HashMap.empty⟩

def push (stx : Syntax) : M Unit := do
  let fmt ← liftCoreM $ do
    let stx ←
      try Lean.PrettyPrinter.parenthesizeCommand stx
      catch e => throw! "failed to parenthesize: {← e.toMessageData.toString}" -- \nin: {stx}"
    try Lean.PrettyPrinter.formatCommand stx
    catch e => throw! "failed to format: {← e.toMessageData.toString}" -- \nin: {stx}"
  modify fun s => { s with output := s.output ++ fmt ++ "\n\n" }

def pushM (stx : M Syntax) : M Unit := stx >>= push

def elabCommand (stx : Syntax) : CommandElabM Unit := do
  -- try dbg_trace "elaborating:\n{← liftCoreM $
  --   Lean.PrettyPrinter.parenthesizeCommand stx >>= Lean.PrettyPrinter.formatCommand}"
  -- catch e => dbg_trace "failed to format: {← e.toMessageData.toString}\nin: {stx}"
  Elab.Command.elabCommand stx

def pushElab (stx : Syntax) : M Unit := elabCommand stx *> push stx

def modifyScope (f : Scope → Scope) : M Unit :=
  modify fun s => { s with current := f s.current }

def pushScope : M Unit :=
  modify fun s => { s with scopes := s.scopes.push s.current }

def popScope : M Unit :=
  modify fun s => match s.scopes.back? with
  | none => s
  | some c => { s with current := c, scopes := s.scopes.pop }

def trDocComment (doc : String) : Syntax :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ "-/")]

partial def scientificLitOfDecimal (num den : Nat) : Option Syntax :=
  findExp num den 0 |>.map fun (m, e) =>
    let str := toString m
    if e == str.length then
      Syntax.mkScientificLit ("0." ++ str)
    else if e < str.length then
      let mStr := str.extract 0 (str.length - e)
      let eStr := str.extract (str.length - e) str.length
      Syntax.mkScientificLit (mStr ++ "." ++ eStr)
    else
      Syntax.mkScientificLit (str ++ "e-" ++ toString e)
where
  findExp n d exp :=
    if d % 10 == 0 then findExp n (d / 10) (exp + 1)
    else if d == 1 then some (n, exp)
    else if d % 2 == 0 then findExp (n * 5) (d / 2) (exp + 1)
    else if d % 5 == 0 then findExp (n * 2) (d / 5) (exp + 1)
    else none

def mkCDot : Syntax := mkNode ``Parser.Term.cdot #[mkAtom "·"]

structure BinderContext where
  -- if true, only allow simple for no type
  allowSimple : Option Bool := none
  requireType := false

partial def trLevel : Level → M Syntax
  | Level.«_» => `(level| _)
  | Level.nat n => Syntax.mkNumLit (toString n)
  | Level.add l n => do `(level| $(← trLevel l.kind) + $(Syntax.mkNumLit (toString n.kind)))
  | Level.imax ls => do `(level| imax $[$(← ls.mapM fun l => trLevel l.kind)]*)
  | Level.max ls => do `(level| max $[$(← ls.mapM fun l => trLevel l.kind)]*)
  | Level.param u => mkIdent u
  | Level.paren l => trLevel l.kind -- do `(level| ($(← trLevel l.kind)))

partial def trPrio : Expr → M Syntax
  | Expr.nat n => Syntax.mkNumLit (toString n)
  | Expr.paren e => trPrio e.kind -- do `(prio| ($(← trPrio e.kind)))
  | _ => throw! "unsupported: advanced prio syntax"

partial def trPrecExpr : Expr → M Syntax
  | Expr.nat n => Syntax.mkNumLit (toString n)
  | Expr.paren e => trPrecExpr e.kind -- do `(prec| ($(← trPrecExpr e.kind)))
  | Expr.ident `max => do `(prec| max)
  | _ => throw! "unsupported: advanced prec syntax"

def trPrec : Precedence → M Syntax
  | Precedence.nat n => Syntax.mkNumLit (toString n)
  | Precedence.expr e => trPrecExpr e.kind

def trBinderName : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkHole arbitrary

def trBinderIdent : BinderName → Syntax
  | BinderName.ident n => mkNode ``binderIdent #[mkIdent n]
  | BinderName.«_» => mkNode ``binderIdent #[mkAtom "_"]

inductive TacticContext | seq | one

def optTy (ty : Option Syntax) : M (Option Syntax) :=
  ty.mapM fun stx => do `(Parser.Term.typeSpec| : $stx)

mutual

  partial def trBlock : Block → (c :_:= TacticContext.seq) → M Syntax
    | ⟨_, none, none, #[]⟩, TacticContext.seq => do `(Parser.Tactic.tacticSeq| {})
    | ⟨_, none, none, tacs⟩, TacticContext.seq => do
      mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented #[
        mkNullNode $ ← tacs.mapM fun tac => do mkGroupNode #[← trTactic tac.kind, mkNullNode]]]
    | bl, TacticContext.one => do `(tactic| · $(← trBlock bl):tacticSeq)
    | ⟨_, cl, cfg, tacs⟩, _ => throw! "unsupported (TODO): block with cfg"

  partial def trTactic : Tactic → (c :_:= TacticContext.one) → M Syntax
    | Tactic.block bl, c => trBlock bl c
    | Tactic.by tac, c => trBlock ⟨true, none, none, #[tac]⟩ c
    | tac, TacticContext.seq => trBlock ⟨true, none, none, #[Spanned.dummy tac]⟩
    | Tactic.«;» tacs, TacticContext.one => do
      let rec build (i : Nat) (lhs : Syntax) : M Syntax :=
        if h : i < tacs.size then do
          match ← trTacticOrList (tacs.get ⟨i, h⟩).kind with
          | Sum.inl tac => `(tactic| $lhs <;> $(← build (i+1) tac))
          | Sum.inr tacs => build (i+1) (← `(tactic| $lhs <;> [$[$tacs],*]))
        else lhs
      build 1 (← trTactic tacs[0].kind)
    | Tactic.«<|>» tacs, TacticContext.one => do
      let tacs ← tacs.mapM fun tac => trTactic tac.kind
      `(tactic| first $[| $tacs]*)
    | Tactic.«[]» tacs, _ => throw! "unsupported (impossible)"
    | Tactic.exact_shortcut e, TacticContext.one => do `(tactic| exact $(← trExpr e.kind))
    | Tactic.expr e, TacticContext.one => do
      match ← trExpr e.kind with
      | `(do $[$els]*) => `(tactic| do $[$els:doElem]*)
      | stx => `(tactic| do $stx:term)
    | Tactic.interactive n args, TacticContext.one => do
      match (← get).tactics.find? n with
      | some f => try f args catch e => throw! "in {n}: {← e.toMessageData.toString}"
      | none => throw! "unsupported tactic {repr n}"

  partial def trTacticOrList : Tactic → M (Sum Syntax (Array Syntax))
    | Tactic.«[]» args => Sum.inr <$> args.mapM fun arg => trTactic arg.kind
    | tac => Sum.inl <$> trTactic tac

end

def trBinderDefault : Default → M Syntax
  | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e.kind))
  | Default.«.» e => do
    `(Parser.Term.binderTactic| := by
      $(← trTactic (Tactic.expr $ e.map Expr.ident) TacticContext.seq):tacticSeq)

def trBinary (n : Name) (lhs rhs : Syntax) : M Syntax := do
  match ← getNotationEntry? n.getString! with
  | some ⟨_, _, NotationKind.unary f, _⟩ => f lhs
  | some ⟨_, _, NotationKind.binary f, _⟩ => f lhs rhs
  | some ⟨_, _, NotationKind.nary f, _⟩ => f #[lhs, rhs]
  | _ =>
    dbg_trace "unsupported binary notation {repr n}"
    mkNode ``Parser.Term.app #[mkIdent n, mkNullNode #[lhs, rhs]]

def expandBinderCollection
  (trBinder : AST3.Binder → Array Syntax → M (Array Syntax)) :
  AST3.Binder → Array Syntax → M (Array Syntax)
| bic@(Binder.collection bi vars n e), out => do
  dbg_trace "expanding binder collection {repr bic}"
  let vars := vars.map $ Spanned.map fun | BinderName.ident v => v | _ => `_x
  let vars1 := vars.map $ Spanned.map BinderName.ident
  let mut out ← trBinder (Binder.binder bi (some vars1) #[] none none) out
  let H := #[Spanned.dummy BinderName._]
  for v in vars do
    let ty := Expr.notation (Choice.one n) #[v.map $ Arg.expr ∘ Expr.ident, e.map Arg.expr]
    out ← trBinder (Binder.binder bi (some H) #[] (some (Spanned.dummy ty)) none) out
  out
| _, _ => unreachable!

mutual

  partial def trDArrow (bis : Array (Spanned Binder)) (ty : Expr) : M Syntax := do
    let bis ← trBinders { requireType := true } bis
    pure $ bis.foldr (init := ← trExpr ty) fun bi ty =>
      mkNode ``Parser.Term.depArrow #[bi, mkAtom "→", ty]

  partial def trBinder : BinderContext → Binder → Array Syntax → M (Array Syntax)
    | _, Binder.binder BinderInfo.instImplicit vars _ (some ty) none, out => do
      let var ← match vars with
      | none => #[]
      | some #[v] => pure #[trBinderName v.kind, mkAtom ":"]
      | some _ => throw! "unsupported (impossible)"
      out.push $ mkNode ``Parser.Term.instBinder
        #[mkAtom "[", mkNullNode var, ← trExpr ty.kind, mkAtom "]"]
    | ⟨allowSimp, req⟩, Binder.binder bi (some vars) bis ty dflt, out => do
      let ty := match req || !bis.isEmpty, ty with
      | true, none => some Expr.«_»
      | _, _ => ty.map (·.kind)
      let ty ← ty.mapM (trDArrow bis)
      let vars := mkNullNode $ vars.map fun v => trBinderName v.kind
      if let some stx ← trSimple allowSimp bi vars ty dflt then return out.push stx
      let ty := @mkNullNode $ match ty with | none => #[] | some ty => #[mkAtom ":", ty]
      if bi == BinderInfo.implicit then
        out.push $ mkNode ``Parser.Term.implicitBinder #[mkAtom "{", vars, ty, mkAtom "}"]
      else
        let dflt ← mkOptionalNode <$> dflt.mapM trBinderDefault
        out.push $ mkNode ``Parser.Term.explicitBinder #[mkAtom "(", vars, ty, dflt, mkAtom ")"]
    | bc, bic@(Binder.collection _ _ _ _), out => expandBinderCollection (trBinder bc) bic out
    | _, Binder.notation _, _ => throw! "unsupported: (notation) binder"
    | _, _, _ => throw! "unsupported (impossible)"
  where
    trSimple
    | some b, BinderInfo.default, vars, ty, none => do
      if b && ty.isSome then return none
      mkNode ``Parser.Term.simpleBinder #[vars, mkOptionalNode (← optTy ty)]
    | _, _, _, _, _ => none

  partial def trBinders (bc : BinderContext) (bis : Array (Spanned Binder)) : M (Array Syntax) := do
    bis.foldlM (fun out bi => trBinder bc bi.kind out) #[]

end

partial def trExplicitBinders : Array (Spanned Binder) → M Syntax
  | #[⟨_, _, Binder.binder _ (some vars) _ ty none⟩] => do
    let ty ← match ty with | none => #[] | some ty => do #[mkAtom ":", ← trExpr ty.kind]
    mkNode ``explicitBinders #[mkNode ``unbracketedExplicitBinders #[
      mkNullNode $ vars.map fun n => trBinderIdent n.kind, mkNullNode ty]]
  | bis => do
    let rec trBinder : AST3.Binder → Array Syntax → M (Array Syntax)
    | Binder.binder _ (some vars) _ ty none, bis => do
      let vars ← vars.mapM fun n => trBinderIdent n.kind
      let ty ← match ty with | none => `(_) | some ty => trExpr ty.kind
      bis.push $ mkNode ``bracketedExplicitBinders #[mkAtom "(", mkNullNode vars, mkAtom ":", ty, mkAtom ")"]
    | bic@(Binder.collection _ _ _ _), bis => expandBinderCollection trBinder bic bis
    | Binder.binder BinderInfo.instImplicit _ _ _ _, _ => throw! "unsupported: instance binder"
    | Binder.notation _, _ => throw! "unsupported: (notation) binder"
    | _, _ => throw! "unsupported (impossible)"
    let bis ← bis.foldlM (fun out bi => trBinder bi.kind out) #[]
    mkNode ``explicitBinders #[mkNullNode bis]

def trLambdaBinder : LambdaBinder → Array Syntax → M (Array Syntax)
  | LambdaBinder.reg bi, out => trBinder { allowSimple := some false } bi out
  | LambdaBinder.«⟨⟩» args, out => do out.push $ ← trExpr (Expr.«⟨⟩» args)

def trOptType (ty : Option Expr) : M (Option Syntax) := ty.mapM trExpr >>= optTy

def trLetDecl : LetDecl → M Syntax
  | LetDecl.var x bis ty val => do
    let letId := mkNode ``Parser.Term.letIdDecl #[
      trBinderName x.kind,
      mkNullNode $ ← trBinders { allowSimple := some true } bis,
      mkOptionalNode $ ← trOptType $ ty.map (·.kind),
      mkAtom ":=", ← trExpr val.kind]
    `(Parser.Term.letDecl| $letId:letIdDecl)
  | LetDecl.pat lhs val => do
    `(Parser.Term.letDecl| $(← trExpr lhs.kind):term := $(← trExpr val.kind))
  | LetDecl.notation n => throw! "unsupported: let notation := ..."

def trArm : Arm → M Syntax
  | ⟨lhs, rhs⟩ => do
    `(Parser.Term.matchAltExpr|
      | $[$(← lhs.mapM fun e => trExpr e.kind)],* => $(← trExpr rhs.kind))

def trDoElem : DoElem → M Syntax
  | DoElem.let decl => do `(doElem| let $(← trLetDecl decl.kind):letDecl)
  | DoElem.eval e => do `(doElem| $(← trExpr e.kind):term)
  | DoElem.«←» lhs ty rhs els => do
    let rhs ← trExpr rhs.kind
    match lhs.kind.unparen, els with
    | Expr.ident lhs, none =>
      `(doElem| let $(mkIdent lhs):ident $[$(← trOptType (ty.map (·.kind)))]? ← $rhs:term)
    | _, _ =>
      let els ← els.mapM fun e => trExpr e.kind
      `(doElem| let $(← trExpr lhs.kind):term ← $rhs:term $[| $els:term]?)

def trProof : Proof → (useFrom : Bool := true) → M Syntax
  | Proof.«from» _ e, useFrom => do
    let e ← trExpr e.kind
    if useFrom then `(Parser.Term.fromTerm| from $e) else e
  | Proof.block bl, _ => do `(by $(← trBlock bl):tacticSeq)
  | Proof.by tac, _ => do `(by $(← trTactic tac.kind TacticContext.seq):tacticSeq)

def trNotation (n : Choice) (args : Array (Spanned Arg)) : M Syntax := do
  let n ← match n with
  | Choice.one n => n
  | Choice.many ns =>
    if ns[1:].all (ns[0] == ·) then ns[0] else
      throw! "unsupported: ambiguous notation"
  match ← getNotationEntry? n.getString!, args.map (·.kind) with
  | some ⟨_, _, NotationKind.const stx, _⟩, #[] => stx
  | some ⟨_, _, NotationKind.const stx, _⟩, _ => throw! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.unary f, _⟩, #[Arg.expr e] => f (← trExpr e)
  | some ⟨_, _, NotationKind.unary f, _⟩, _ => throw! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binary f, _⟩, #[Arg.expr e₁, Arg.expr e₂] => f (← trExpr e₁) (← trExpr e₂)
  | some ⟨_, _, NotationKind.binary f, _⟩, _ => throw! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.nary f, _⟩, args => f <$> args.mapM fun
    | Arg.expr e => trExpr e
    | Arg.binder bi => trExplicitBinders #[Spanned.dummy bi]
    | Arg.binders bis => trExplicitBinders bis
    | _ => throw! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.exprs f, _⟩, #[Arg.exprs es] => f $ ← es.mapM fun e => trExpr e.kind
  | some ⟨_, _, NotationKind.exprs f, _⟩, _ => throw! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binder f, _⟩, #[Arg.binder bi, Arg.expr e] => do
    f (← trExplicitBinders #[Spanned.dummy bi]) (← trExpr e)
  | some ⟨_, _, NotationKind.binder f, _⟩, #[Arg.binders bis, Arg.expr e] => do
    if bis.isEmpty then trExpr e else f (← trExplicitBinders bis) (← trExpr e)
  | some ⟨_, _, NotationKind.binder f, _⟩, _ => throw! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.fail, _⟩, args =>
    dbg_trace "unsupported notation {repr n}"
    let args ← args.mapM fun | Arg.expr e => trExpr e | _ => throw! "unsupported notation {repr n}"
    mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]
  | none, args =>
    dbg_trace "unsupported notation {repr n}"
    let args ← args.mapM fun | Arg.expr e => trExpr e | _ => throw! "unsupported notation {repr n}"
    mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]

def trInfixFn (n : Choice) (e : Option (Spanned Expr)) : M Syntax := do
  let n ← match n with
  | Choice.one n => n
  | Choice.many ns =>
    if ns[1:].all (ns[0] == ·) then ns[0] else
      throw! "unsupported: ambiguous notation"
  trBinary n mkCDot $ ← match e with
  | none => mkCDot
  | some e => trExpr e.kind

partial def trAppArgs [Inhabited α] : (e : Expr) → (m : Expr → M α) → M (α × Array Syntax)
  | Expr.app f x, m => do let (f, args) ← trAppArgs f.kind m; (f, args.push (← trExpr x.kind))
  | e, m => do (← m e, #[])

def trExpr' : Expr → M Syntax
  | Expr.«...» => `(Parser.Term.calcDots| ...)
  | Expr.sorry => `(sorry)
  | Expr.«_» => `(_)
  | Expr.«()» => `(())
  | Expr.«{}» => `({})
  | Expr.ident n => mkIdentI n
  | Expr.const _ n none => mkIdentI n.kind
  | Expr.const _ n (some #[]) => mkIdentI n.kind
  | Expr.const _ n (some l) => do
    mkNode ``Parser.Term.explicitUniv #[← mkIdentI n.kind,
      mkAtom ".{", (mkAtom ",").mkSep $ ← l.mapM fun e => trLevel e.kind, mkAtom "}"]
  | Expr.nat n => Syntax.mkNumLit (toString n)
  | Expr.decimal n d => (scientificLitOfDecimal n d).get!
  | Expr.string s => Syntax.mkStrLit s
  | Expr.char c => Syntax.mkCharLit c
  | Expr.paren e => trExpr e.kind -- do `(($(← trExpr e.kind)))
  | Expr.sort ty st u => do
    match ty, if st then some Level._ else u.map Spanned.kind with
    | false, none => `(Sort)
    | false, some u => do `(Sort $(← trLevel u))
    | true, none => `(Type)
    | true, some u => do `(Type $(← trLevel u))
  | Expr.«→» lhs rhs => do `($(← trExpr lhs.kind) → $(← trExpr rhs.kind))
  | Expr.fun true #[⟨_, _, LambdaBinder.reg (Binder.binder _ none _ (some ty) _)⟩] e => do
    `(fun $(mkIdent `this):ident: $(← trExpr ty.kind) => $(← trExpr e.kind))
  | Expr.fun _ bis e => do
    let bis ← bis.foldlM (fun out bi => trLambdaBinder bi.kind out) #[]
    `(fun $[$bis]* => $(← trExpr e.kind))
  | Expr.Pi bis e => do
    -- let dArrowHeuristic := !bis.any fun | ⟨_, _, Binder.binder _ _ _ none _⟩ => true | _ => false
    let dArrowHeuristic := false
    if dArrowHeuristic then trDArrow bis e.kind else
      `(∀ $[$(← trBinders { allowSimple := some false } bis)]*, $(← trExpr e.kind))
  | e@(Expr.app _ _) => do
    let (f, args) ← trAppArgs e trExpr
    mkNode ``Parser.Term.app #[f, mkNullNode args]
  | Expr.show t pr => do
    mkNode ``Parser.Term.show #[mkAtom "show", ← trExpr t.kind, ← trProof pr.kind]
  | Expr.have true h t pr e => do
    let decl := mkNode ``Parser.Term.sufficesDecl #[
      mkOptionalNode $ h.map fun h => mkIdent h.kind, ← trExpr t.kind, ← trProof pr.kind]
    mkNode ``Parser.Term.suffices #[mkAtom "suffices", decl, mkNullNode, ← trExpr e.kind]
  | Expr.have false h t pr e => do
    let t := match t.kind with | Expr._ => none | t => some t
    let haveId := mkNode ``Parser.Term.haveIdDecl #[
      mkNullNode $ match h with | none => #[] | some h => #[mkIdent h.kind, mkNullNode],
      mkOptionalNode $ ← trOptType t, mkAtom ":=", ← trProof pr.kind false]
    mkNode ``Parser.Term.have #[mkAtom "have",
      mkNode ``Parser.Term.haveDecl #[haveId], mkNullNode, ← trExpr e.kind]
  | Expr.«.» _ e pr => do
    let pr ← match pr.kind with
    | Lean3.Proj.ident e => mkIdentF e
    | Lean3.Proj.nat n => Syntax.mkLit fieldIdxKind (toString n)
    mkNode ``Parser.Term.proj #[← trExpr e.kind, mkAtom ".", pr]
  | Expr.if none c t e => do
    `(if $(← trExpr c.kind) then $(← trExpr t.kind) else $(← trExpr e.kind))
  | Expr.if (some h) c t e => do
    `(if $(mkIdent h.kind):ident : $(← trExpr c.kind)
      then $(← trExpr t.kind) else $(← trExpr e.kind))
  | Expr.calc args => do
    let (lhs, rhs) := args[0]
    mkNode ``Parser.Term.calc #[mkAtom "calc",
      mkNode ``Parser.Term.calcFirst #[← trExpr lhs.kind, mkAtom ":", ← trExpr rhs.kind],
      mkNullNode $ ← args[1:].toArray.mapM fun (lhs, rhs) => do
        mkNode ``Parser.Term.calcRest #[← trExpr lhs.kind, mkAtom ":", ← trExpr rhs.kind]]
  | Expr.«@» _ e => do `(@$(← trExpr e.kind))
  | Expr.pattern e => trExpr e.kind
  | Expr.«`()» _ true e => do `(quote $(← trExpr e.kind))
  | Expr.«`()» false false e => do `(pquote $(← trExpr e.kind))
  | Expr.«`()» true false e => do `(ppquote $(← trExpr e.kind))
  | Expr.«%%» e => do `(%%$(← trExpr e.kind))
  | Expr.«`[]» tacs => throw! "unsupported (TODO): `[tacs]"
  | Expr.«`» false n => `($(Syntax.mkNameLit s!"`{n}"):nameLit)
  | Expr.«`» true n => do `(``$(← mkIdentI n):ident)
  | Expr.«⟨⟩» es => do `(⟨$[$(← es.mapM fun e => trExpr e.kind)],*⟩)
  | Expr.infix_fn n e => trInfixFn n e
  | Expr.«(,)» es => do
    `(($(← trExpr es[0].kind):term, $[$(← es[1:].toArray.mapM fun e => trExpr e.kind)],*))
  | Expr.«.()» e => trExpr e.kind
  | Expr.«:» e ty => do `(($(← trExpr e.kind) : $(← trExpr ty.kind)))
  | Expr.hole es => throw! "unsupported: \{! ... !}"
  | Expr.«#[]» es => throw! "unsupported: #[...]"
  | Expr.by tac => do `(by $(← trTactic tac.kind TacticContext.seq):tacticSeq)
  | Expr.begin tacs => do `(by $(← trBlock tacs):tacticSeq)
  | Expr.let bis e => do
    bis.foldrM (init := ← trExpr e.kind) fun bi stx => do
      `(let $(← trLetDecl bi.kind):letDecl $stx)
  | Expr.match #[x] _ #[] => do `(nomatch $(← trExpr x.kind))
  | Expr.match xs _ #[] => do `(match $[$(← xs.mapM fun x => trExpr x.kind):term],* with.)
  | Expr.match xs ty eqns => do
    `(match $[$(← xs.mapM fun x => trExpr x.kind):term],* with $[$(← eqns.mapM trArm):matchAlt]*)
  | Expr.do _ els => do let els ← els.mapM fun e => trDoElem e.kind; `(do $[$els:doElem]*)
  | Expr.«{,}» es => do `({$[$(← es.mapM fun e => trExpr e.kind)],*})
  | Expr.subtype false x ty p => do
    `({$(mkIdent x.kind) $[: $(← ty.mapM fun e => trExpr e.kind)]? // $(← trExpr p.kind)})
  | Expr.subtype true x ty p => do
    `({$(mkIdent x.kind) $[: $(← ty.mapM fun e => trExpr e.kind)]? | $(← trExpr p.kind)})
  | Expr.sep x ty p => do
    `({$(mkIdent x.kind) ∈ $(← trExpr ty.kind) | $(← trExpr p.kind)})
  | Expr.setReplacement e bis => do
    `({$(← trExpr e.kind) | $[$(← trBinders {} bis):bracketedBinder]*})
  | Expr.structInst _ src flds srcs catchall => do
    let src ← src.mapM fun s => trExpr s.kind
    let flds := flds ++ srcs.map fun e => (Spanned.dummy `__, e)
    let flds ← flds.mapM fun (⟨_, _, lhs⟩, ⟨_, _, rhs⟩) => do
      if (match rhs with | Expr.ident rhs => rhs == lhs | _ => false : Bool) then
        `(Parser.Term.structInstFieldAbbrev| $(← mkIdentF lhs):ident)
      else
        `(Parser.Term.structInstField| $(← mkIdentF lhs):ident := $(← trExpr rhs))
    -- TODO(Mario): formatter has trouble if you omit the commas
    if catchall then
      `({ $[$src with]? $[$flds:structInstField, ]* .. })
    else if let some last := flds.back? then
      `({ $[$src with]? $[$(flds.pop):structInstField, ]* $last:structInstField })
    else
      `({ $[$src with]? })
  | Expr.atPat lhs rhs => do `($(mkIdent lhs.kind)@ $(← trExpr rhs.kind))
  | Expr.notation n args => trNotation n args
  | Expr.userNotation n args => do
    match (← get).userNota.find? n with
    | some f => try f args catch e => throw! "in {n}: {← e.toMessageData.toString}"
    | none => throw! "unsupported user notation {n}"

inductive TrAttr
  | del : Syntax → TrAttr
  | add : Syntax → TrAttr
  | prio : Expr → TrAttr
  | parsingOnly : TrAttr
  | unify : TrAttr

def trAttr (prio : Option Expr) : Attribute → M (Option TrAttr)
  | Attribute.priority n => TrAttr.prio n.kind
  | Attribute.del n => do
    let n ← match n with
    | `instance => `instance
    | `simp => `simp
    | `congr => `congr
    | `inline => `inline
    | `pattern => `matchPattern
    | _ =>
      dbg_trace "unsupported attr -{n}"
      return none
    TrAttr.del (← `(Parser.Command.eraseAttr| -$(← mkIdentI n)))
  | AST3.Attribute.add `parsing_only none => TrAttr.parsingOnly
  | AST3.Attribute.add `unify none => TrAttr.unify
  | AST3.Attribute.add n arg => do
    let mkSimpleAttr n (args := #[]) := do
      mkNode ``Parser.Attr.simple #[← mkIdentI n, mkNullNode args]
    let attr ← match n, arg with
    | `class,         none => `(attr| class)
    | `instance,      none => `(attr| instance)
    | `simp,          none => `(attr| simp)
    | `recursor,      some ⟨_, _, AttrArg.indices #[]⟩ => throw! "unsupported: @[recursor]"
    | `recursor,      some ⟨_, _, AttrArg.indices #[⟨_, _, n⟩]⟩ =>
      `(attr| recursor $(Syntax.mkNumLit (toString n)):numLit)
    | `congr,         none => mkSimpleAttr `congr
    | `inline,        none => mkSimpleAttr `inline
    | `pattern,       none => mkSimpleAttr `matchPattern
    | `reducible,     none => mkSimpleAttr `reducible
    | `semireducible, none => mkSimpleAttr `semireducible
    | `irreducible,   none => mkSimpleAttr `irreducible
    | `elab_simple,   none => mkSimpleAttr `elabWithoutExpectedType
    | `vm_override,   some ⟨_, _, AttrArg.vmOverride n none⟩ =>
      mkSimpleAttr `implementedBy #[← mkIdentI n.kind]
    | _, _ =>
      if builtinAttributes.contains n then
        dbg_trace "suppressing unsupported attr {n}"
      else if (← get).simpSets.contains n then
        dbg_trace "suppressing simp set attr {n}"
      else
        dbg_trace "suppressing unknown attr {n}"
      return none
    TrAttr.add attr

def trAttrKind : AttributeKind → M Syntax
  | AttributeKind.global => `(Parser.Term.attrKind|)
  | AttributeKind.scoped => `(Parser.Term.attrKind| scoped)
  | AttributeKind.local => `(Parser.Term.attrKind| local)

structure SpecialAttrs where
  prio : Option AST3.Expr := none
  parsingOnly := false
  unify := false

def AttrState := SpecialAttrs × Array Syntax

def trAttrInstance (attr : Attribute) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit := do
  match ← trAttr (← get).1.prio attr with
  | some (TrAttr.del stx) => do
    unless allowDel do throw! "unsupported (impossible)"
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.add stx) => do
    let stx := mkNode ``Parser.Term.attrInstance #[← trAttrKind kind, stx]
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.prio prio) => modify fun s => { s with 1.prio := prio }
  | some TrAttr.parsingOnly => modify fun s => { s with 1.parsingOnly := true }
  | some TrAttr.unify => modify fun s => { s with 1.unify := true }
  | none => pure ()

def trAttributes (attrs : Attributes) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit :=
  attrs.forM fun attr => trAttrInstance attr.kind allowDel kind

structure Modifiers4 where
  docComment : Option String := none
  attrs : AttrState := ({}, #[])
  vis : Visibility := Visibility.regular
  «noncomputable» : Option Unit := none
  safety : DefinitionSafety := DefinitionSafety.safe

def mkOpt (a : Option α) (f : α → M Syntax) : M Syntax :=
  match a with
  | none => mkNullNode
  | some a => do mkNullNode #[← f a]

def trModifiers (mods : Modifiers) : M (SpecialAttrs × Syntax) :=
  mods.foldlM trModifier {} >>= toSyntax
where
  trModifier (s : Modifiers4) (m : Spanned Modifier) : M Modifiers4 :=
    match m.kind with
    | Modifier.private => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.private }
      | _ => throw! "unsupported (impossible)"
    | Modifier.protected => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.protected }
      | _ => throw! "unsupported (impossible)"
    | Modifier.noncomputable => match s.noncomputable with
      | none => pure { s with «noncomputable» := some () }
      | _ => throw! "unsupported (impossible)"
    | Modifier.meta => match s.safety with
      | DefinitionSafety.safe => pure { s with safety := DefinitionSafety.unsafe }
      | _ => throw! "unsupported (impossible)"
    | Modifier.mutual => s -- mutual is duplicated elsewhere in the grammar
    | Modifier.attr loc _ attrs => do
      let kind := if loc then AttributeKind.local else AttributeKind.global
      pure { s with attrs := (← trAttributes attrs false kind |>.run ({}, #[])).2 }
    | Modifier.doc doc => match s.docComment with
      | none => pure { s with docComment := some doc }
      | _ => throw! "unsupported (impossible)"
  toSyntax : Modifiers4 → M (SpecialAttrs × Syntax)
  | ⟨doc, (s, attrs), vis, nc, safety⟩ => do
    let doc := mkOptionalNode $ doc.map trDocComment
    let attrs ← mkOpt (if attrs.isEmpty then none else some attrs) fun attrs =>
      `(Parser.Term.attributes| @[$[$attrs],*])
    let vis := mkOptionalNode $ ← match vis with
    | Visibility.regular => none
    | Visibility.private => `(Parser.Command.visibility| private)
    | Visibility.protected => `(Parser.Command.visibility| protected)
    let nc ← mkOpt nc fun () => `(Parser.Command.noncomputable| noncomputable)
    let part := mkOptionalNode $ ← match safety with
    | DefinitionSafety.partial => some <$> `(Parser.Command.partial| partial)
    | _ => none
    let uns := mkOptionalNode $ ← match safety with
    | DefinitionSafety.unsafe => some <$> `(Parser.Command.unsafe| unsafe)
    | _ => none
    (s, mkNode ``Parser.Command.declModifiers #[doc, attrs, vis, nc, uns, part])

def trOpenCmd (ops : Array Open) : M Unit := do
  let mut simple := #[]
  let pushSimple (s : Array Syntax) :=
    unless s.isEmpty do pushElab $ ← `(command| open $[$s]*)
  for o in ops do
    match o with
    | ⟨tgt, none, clauses⟩ =>
      if clauses.isEmpty then
        simple := simple.push (← mkIdentN tgt.kind)
      else
        pushSimple simple; simple := #[]
        let mut explicit := #[]
        let mut renames := #[]
        let mut hides := #[]
        for c in clauses do
          match c.kind with
          | OpenClause.explicit ns => explicit := explicit ++ ns
          | OpenClause.renaming ns => renames := renames ++ ns
          | OpenClause.hiding ns => hides := hides ++ ns
        match explicit.isEmpty, renames.isEmpty, hides.isEmpty with
        | true, true, true => pure ()
        | false, true, true =>
          let ns ← explicit.mapM fun n => mkIdentF n.kind
          pushElab $ ← `(command| open $(mkIdent tgt.kind):ident ($[$ns]*))
        | true, false, true =>
          let rs ← renames.mapM fun ⟨a, b⟩ => do
            `(Parser.Command.openRenamingItem|
              $(← mkIdentF a.kind):ident → $(← mkIdentF b.kind):ident)
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident renaming $[$rs],*)
        | true, true, false =>
          let ns ← hides.mapM fun n => mkIdentF n.kind
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident hiding $[$ns]*)
        | _, _, _ => throw! "unsupported: advanced open style"
    | _ => throw! "unsupported: unusual advanced open style"
  pushSimple simple

def trExportCmd : Open → M Unit
  | ⟨tgt, none, clauses⟩ => do
    let mut args := #[]
    for c in clauses do
      match c.kind with
      | OpenClause.explicit ns =>
        for n in ns do args := args.push (← mkIdentF n.kind)
      | _ => throw! "unsupported: advanced export style"
    pushElab $ ← `(export $(← mkIdentN tgt.kind):ident ($[$args]*))
  | _ => throw! "unsupported: advanced export style"

def trDeclId (n : Name) (us : LevelDecl) : M Syntax := do
  let us := us.map $ Array.map fun u => mkIdent u.kind
  `(Parser.Command.declId| $(← mkIdentI n):ident $[.{$[$us],*}]?)

def trDeclSig (req : Bool) (bis : Binders) (ty : Option (Spanned Expr)) : M Syntax := do
  let bis := mkNullNode (← trBinders { allowSimple := some true } bis)
  let ty := ty.map Spanned.kind
  let ty ← trOptType $ if req then some (ty.getD Expr.«_») else ty
  if req then mkNode ``Parser.Command.declSig #[bis, ty.get!]
  else mkNode ``Parser.Command.optDeclSig #[bis, mkOptionalNode ty]

def trAxiom (mods : Modifiers) (n : Name)
  (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr)) : M Unit := do
  let (_, mods) ← trModifiers mods
  pushM `(command| $mods:declModifiers axiom $(← trDeclId n us) $(← trDeclSig true bis ty))

def trDecl (dk : DeclKind) (mods : Modifiers) (n : Option (Spanned Name)) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr)) (val : DeclVal) : M (Option Syntax) := do
  let (s, mods) ← trModifiers mods
  if s.unify then return none
  let id ← n.mapM fun n => trDeclId n.kind us
  let sig req := trDeclSig req bis ty
  let val ← match val with
  | DeclVal.expr e => do `(Parser.Command.declValSimple| := $(← trExpr e))
  | DeclVal.eqns #[] => `(Parser.Command.declValSimple| := fun.)
  | DeclVal.eqns arms => do `(Parser.Command.declValEqns| $[$(← arms.mapM trArm):matchAlt]*)
  match dk with
  | DeclKind.abbrev => do `(command| $mods:declModifiers abbrev $id.get! $(← sig false) $val)
  | DeclKind.def => do `(command| $mods:declModifiers def $id.get! $(← sig false) $val)
  | DeclKind.example => do `(command| $mods:declModifiers example $(← sig true) $val)
  | DeclKind.theorem => do `(command| $mods:declModifiers theorem $id.get! $(← sig true) $val)
  | DeclKind.instance => do
    let prio ← s.prio.mapM fun prio => do
      `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
    `(command| $mods:declModifiers instance $[$prio:namedPrio]? $[$id:declId]? $(← sig true) $val)

def trInferKind : Option InferKind → M (Option Syntax)
  | some InferKind.implicit => `(Parser.Command.inferMod | {})
  | some InferKind.relaxedImplicit => `(Parser.Command.inferMod | {})
  | some InferKind.none => none
  | none => none

def trInductive (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr))
  (nota : Option Notation) (intros : Array (Spanned Intro)) : M Syntax := do
  let (prio, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let sig ← trDeclSig false bis ty
  let ctors ← intros.mapM fun ⟨_, _, ⟨doc, name, ik, bis, ty⟩⟩ => do
    `(Parser.Command.ctor| |
      $[$(doc.map trDocComment):docComment]?
      $(← mkIdentI name.kind):ident
      $[$(← trInferKind ik):inferMod]?
      $(← trDeclSig false bis ty):optDeclSig)
  if cl then
    `(command| $mods:declModifiers class inductive $id:declId $sig:optDeclSig $[$ctors:ctor]*)
  else
    `(command| $mods:declModifiers inductive $id:declId $sig:optDeclSig $[$ctors:ctor]*)

def trMutual (decls : Array (Mutual α)) (f : Mutual α → M Syntax) : M Unit := do
  pushM `(mutual $[$(← decls.mapM f)]* end)

def trField : Field → Array Syntax → M (Array Syntax)
  | Field.binder bi ns ik bis ty dflt, out => do
    let ns ← ns.mapM fun n => mkIdentF n.kind
    let im ← trInferKind ik
    let sig req := trDeclSig req bis ty
    out.push <$> match bi with
    | BinderInfo.implicit => do
      `(Parser.Command.structImplicitBinder| {$[$ns]* $[$im]? $(← sig true):declSig})
    | BinderInfo.instImplicit => do
      `(Parser.Command.structInstBinder| [$[$ns]* $[$im]? $(← sig true):declSig])
    | _ => do
      let sig ← sig false
      let dflt ← dflt.mapM trBinderDefault
      if ns.size = 1 then
        `(Parser.Command.structSimpleBinder| $(ns[0]):ident $[$im]? $sig:optDeclSig $[$dflt]?)
      else
        `(Parser.Command.structExplicitBinder| ($[$ns]* $[$im]? $sig:optDeclSig $[$dflt]?))
  | Field.notation _, out => throw! "unsupported: (notation) in structure"

def trFields (flds : Array (Spanned Field)) : M Syntax := do
  let flds ← flds.foldlM (fun out fld => trField fld.kind out) #[]
  mkNode ``Parser.Command.structFields #[mkNullNode flds]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let (prio, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let bis := mkNullNode $ ← trBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, _, false, none, ty, #[]⟩ => trExpr ty.kind
    | _ => throw! "unsupported: advanced extends in structure"
  let exts ← mkOpt (if exts.isEmpty then none else some exts) fun exts =>
    `(Parser.Command.extends| extends $[$exts],*)
  let ty ← mkOptionalNode <$> trOptType (ty.map Spanned.kind)
  let flds ← @mkNullNode <$> match mk, flds with
  | none, #[] => #[]
  | mk, flds => do
    let mk ← mk.mapM fun ⟨_, _, n, ik⟩ => do
      `(Parser.Command.structCtor| $(← mkIdentF n.kind):ident $[$(← trInferKind ik)]? ::)
    #[mkAtom "where", mkOptionalNode mk, ← trFields flds]
  let decl := mkNode ``Parser.Command.structure #[
    ← if cl then `(Parser.Command.classTk| class) else `(Parser.Command.structureTk| structure),
    id, bis, exts, ty, flds, ← `(Parser.Command.optDeriving|)]
  pushM `(command| $mods:declModifiers $decl:structure)

partial def mkUnusedName [Monad m] [MonadResolveName m] [MonadEnv m]
  (baseName : Name) : m Name := do
  let ns ← getCurrNamespace
  let env ← getEnv
  if env.contains (ns ++ baseName) then
    let rec loop (idx : Nat) := do
      let name := baseName.appendIndexAfter idx
      if env.contains (ns ++ name) then loop (idx+1) else name
    loop 1
  else baseName

section

private def mkNAry (lits : Array (Spanned AST3.Literal)) : OptionM (Array Literal) := do
  let mut i := 0
  let mut out := #[]
  for lit in lits do
    match lit with
    | ⟨_, _, AST3.Literal.sym tk⟩ => out := out.push (Literal.tk tk.1.kind.toString)
    | ⟨_, _, AST3.Literal.var _ _⟩ => out := out.push (Literal.arg i); i := i + 1
    | ⟨_, _, AST3.Literal.binder _⟩ => out := out.push (Literal.arg i); i := i + 1
    | ⟨_, _, AST3.Literal.binders _⟩ => out := out.push (Literal.arg i); i := i + 1
    | _ => none
  out

private def isIdentPrec : AST3.Literal → Bool
  | AST3.Literal.sym _ => true
  | AST3.Literal.var _ none => true
  | AST3.Literal.var _ (some ⟨_, _, Action.prec _⟩) => true
  | _ => false

private def trMixfix (kind : Syntax) (prio : Option Syntax)
  (m : AST3.MixfixKind) (tk : String) (prec : Option (Spanned AST3.Precedence)) :
  M (NotationDesc × (Option Syntax → Syntax → Id Syntax)) := do
  let p ← match prec with | some p => trPrec p.kind | none => `(prec| 0)
  let s := Syntax.mkStrLit tk
  match m with
  | MixfixKind.infix =>
    (NotationDesc.infix tk, fun n e => `(command|
      $kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixl =>
    (NotationDesc.infix tk, fun n e => `(command|
      $kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixr =>
    (NotationDesc.infix tk, fun n e => `(command|
      $kind:attrKind infixr:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.prefix =>
    (NotationDesc.prefix tk, fun n e => `(command|
      $kind:attrKind prefix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.postfix =>
    (NotationDesc.postfix tk, fun n e => `(command|
      $kind:attrKind postfix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))

private def trNotation4 (kind : Syntax) (prio p : Option Syntax)
  (lits : Array (Spanned AST3.Literal)) : M (Option Syntax → Syntax → Id Syntax) := do
  let lits ← lits.mapM fun
  | ⟨_, _, AST3.Literal.sym tk⟩ => Syntax.mkStrLit tk.1.kind.toString
  | ⟨_, _, AST3.Literal.var x none⟩ =>
    `(Parser.Command.identPrec| $(mkIdent x.kind):ident)
  | ⟨_, _, AST3.Literal.var x (some ⟨_, _, Action.prec p⟩)⟩ => do
    `(Parser.Command.identPrec| $(mkIdent x.kind):ident : $(← trPrec p))
  | _ => throw! "unsupported (impossible)"
  pure fun n e => `(command|
    $kind:attrKind notation$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $[$lits]* => $e)

private def trNotation3Item (lit : AST3.Literal) : M Syntax := do
  let stxs ← match lit with
  | AST3.Literal.sym tk => sym tk
  | AST3.Literal.binder _ => binders
  | AST3.Literal.binders _ => binders
  | AST3.Literal.var x none => var x
  | AST3.Literal.var x (some ⟨_, _, Action.prec _⟩) => var x
  | AST3.Literal.var x (some ⟨_, _, Action.prev⟩) => var x
  | AST3.Literal.var x (some ⟨_, _, Action.scoped _ sc⟩) => scope x sc
  | _ => throw! "unsupported: advanced notation"
  mkNode ``Parser.Command.notation3Item stxs
where
  sym tk := #[Syntax.mkStrLit tk.1.kind.toString]
  var x := #[mkIdent x.kind, mkNullNode]
  binders := #[mkNode ``Parser.Command.bindersItem #[mkAtom "(", mkAtom "...", mkAtom ")"]]
  scope x sc := do
    let (p, e) := match sc with
    | none => (`x, Expr.ident `x)
    | some (p, e) => (p.kind, e.kind)
    #[mkIdent x.kind, mkNullNode #[
      mkNode ``Parser.Command.identScope #[
        mkAtom ":", mkAtom "(", mkAtom "scoped",
        mkIdent p, mkAtom "=>", ← trExpr e, mkAtom ")"]]]

private def trNotation3 (kind : Syntax) (prio p : Option Syntax)
  (lits : Array (Spanned AST3.Literal)) : M (Option Syntax → Syntax → Id Syntax) := do
  let lits ← lits.mapM fun lit => trNotation3Item lit.kind
  pure fun n e => `(command|
    $kind:attrKind notation3$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $[$lits]* => $e)

def trNotationCmd (loc : LocalReserve) (attrs : Attributes) (nota : Notation) : M Unit := do
  let (s, attrs) := (← trAttributes attrs false AttributeKind.global |>.run ({}, #[])).2
  unless attrs.isEmpty do throw! "unsupported (impossible)"
  if loc.2 then return
  let kind ← if loc.1 then `(Parser.Term.attrKind| local) else `(Parser.Term.attrKind|)
  let n := nota.name3
  let skip : Bool := match ← getNotationEntry? n with
  | some ⟨_, _, _, skip⟩ => skip
  | none => false
  if skip && !loc.1 then return
  let prio ← s.prio.mapM fun prio => do
    `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
  let (e, desc, cmd) ← match nota with
  | Notation.mixfix m (tk, prec) (some e) =>
    (e, ← trMixfix kind prio m tk.kind.toString prec)
  | Notation.notation lits (some e) =>
    let p ← match lits.get? 0 with
    | some ⟨_, _, AST3.Literal.sym tk⟩ => tk.2.mapM fun p => trPrec p.kind
    | some ⟨_, _, AST3.Literal.var _ _⟩ => match lits.get? 1 with
      | some ⟨_, _, AST3.Literal.sym tk⟩ => tk.2.mapM fun p => trPrec p.kind
      | _ => none
    | _ => none
    let desc := match lits with
    | #[⟨_, _, AST3.Literal.sym tk⟩] => NotationDesc.const tk.1.kind.toString
    | _ => match mkNAry lits with
      | some lits => NotationDesc.nary lits
      | none => NotationDesc.fail
    let cmd ← match lits.all fun lit => isIdentPrec lit.kind with
    | true => trNotation4 kind prio p lits
    | false => trNotation3 kind prio p lits
    (e, desc, cmd)
  | _ => throw! "unsupported (impossible)"
  let e ← trExpr e.kind
  let n4 ← Elab.Command.withWeakNamespace (← getEnv).mainModule $ do
    let n4 ← mkUnusedName nota.name4
    let nn ← `(Parser.Command.namedName| (name := $(mkIdent n4)))
    try elabCommand $ cmd (some nn) e
    catch e => dbg_trace "failed to add syntax {repr n4}: {← e.toMessageData.toString}"
    pure $ (← getCurrNamespace) ++ n4
  push $ cmd none e
  registerNotationEntry ⟨n, n4, desc⟩

end

def trInductiveCmd : InductiveCmd → M Unit
  | InductiveCmd.reg cl mods n us bis ty nota intros =>
     pushM $ trInductive cl mods n us bis ty nota intros
  | InductiveCmd.mutual cl mods us bis nota inds =>
    trMutual inds fun ⟨attrs, n, ty, intros⟩ => do
      trInductive cl mods n us bis ty nota intros

def trCommand' : Command → M Unit
  | Command.initQuotient => pushM `(init_quot)
  | Command.mdoc doc =>
    push $ mkNode ``Parser.Command.modDocComment #[mkAtom "/!", mkAtom (doc ++ "-/")]
  | Command.«universe» _ _ ns =>
    pushM `(universe $[$(ns.map fun n => mkIdent n.kind)]*)
  | Command.«namespace» n => do
    pushScope; modifyScope fun s => { s with curNamespace := s.curNamespace ++ n.kind }
    pushElab $ ← `(namespace $(← mkIdentN n.kind))
  | Command.«section» n => do
    pushScope; pushElab $ ← `(section $[$(← n.mapM fun n => mkIdentN n.kind)]?)
  | Command.«end» n => do
    popScope; pushElab $ ← `(end $[$(← n.mapM fun n => mkIdentN n.kind)]?)
  | Command.«variable» vk _ _ bis =>
    unless bis.isEmpty do
      let bis ← trBinders {} bis
      match vk with
      | VariableKind.variable => pushM `(variable $[$bis]*)
      | VariableKind.parameter => pushM `(parameter $[$bis]*)
  | Command.axiom _ mods n us bis ty => trAxiom mods n.kind us bis ty
  | Command.axioms _ mods bis => bis.forM fun
    | ⟨_, _, Binder.binder _ (some ns) bis (some ty) none⟩ => ns.forM fun
      | ⟨_, _, BinderName.ident n⟩ => trAxiom mods n none bis ty
      | _ => throw! "unsupported (impossible)"
    | _ => throw! "unsupported (impossible)"
  | Command.decl dk mods n us bis ty val => do
    if let some decl ← trDecl dk mods n us bis ty val.kind then
      push decl
  | Command.mutualDecl dk mods us bis arms =>
    trMutual arms fun ⟨attrs, n, ty, vals⟩ => do
      match ← trDecl dk mods n us bis ty (DeclVal.eqns vals) with
      | none => throw! "unsupported: mutual @[unify]"
      | some decl => decl
  | Command.inductive ind => trInductiveCmd ind
  | Command.structure cl mods n us bis exts ty m flds =>
    trStructure cl mods n us bis exts ty m flds
  | Command.attribute loc _ attrs ns => do
    let kind := if loc then AttributeKind.local else AttributeKind.global
    let attrs := (← trAttributes attrs true kind |>.run ({}, #[])).2.2
    if attrs.isEmpty || ns.isEmpty then return ()
    let ns ← ns.mapM fun n => mkIdentI n.kind
    pushM `(command| attribute [$[$attrs],*] $[$ns]*)
  | Command.precedence sym prec => pure ()
  | Command.notation loc attrs n => trNotationCmd loc attrs n
  | Command.open true ops => ops.forM trExportCmd
  | Command.open false ops => trOpenCmd ops
  | Command.include true ops => unless ops.isEmpty do
      pushM `(include $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.include false ops => unless ops.isEmpty do
      pushM `(omit $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.hide ops => unless ops.isEmpty do
      throw! "unsupported: hide command"
      -- pushM `(hide $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.theory #[⟨_, _, Modifier.noncomputable⟩] =>
    pushM `(command| noncomputable theory)
  | Command.theory #[⟨_, _, Modifier.doc doc⟩, ⟨_, _, Modifier.noncomputable⟩] =>
    pushM `(command| $(trDocComment doc):docComment noncomputable theory)
  | Command.theory _ => throw! "unsupported (impossible)"
  | Command.setOption o val => match o.kind, val.kind with
    | `old_structure_cmd, OptionVal.bool b =>
      modifyScope fun s => { s with oldStructureCmd := b }
    | o, OptionVal.bool true => do
      pushM `(command| set_option $(← mkIdentO o) true)
    | o, OptionVal.bool false => do
      pushM `(command| set_option $(← mkIdentO o) false)
    | o, OptionVal.str s => do
      pushM `(command| set_option $(← mkIdentO o) $(Syntax.mkStrLit s):strLit)
    | o, OptionVal.nat n => do
      pushM `(command| set_option $(← mkIdentO o) $(Syntax.mkNumLit (toString n)):numLit)
    | o, OptionVal.decimal _ _ => throw! "unsupported: float-valued option"
  | Command.declareTrace n => throw! "unsupported (TODO): declare_trace"
  | Command.addKeyEquivalence a b => throw! "unsupported: add_key_equivalence"
  | Command.runCmd e => do pushM `(run_cmd $(← trExpr e.kind))
  | Command.check e => do pushM `(#check $(← trExpr e.kind))
  | Command.reduce _ e => do pushM `(#reduce $(← trExpr e.kind))
  | Command.eval e => do pushM `(#eval $(← trExpr e.kind))
  | Command.unify e₁ e₂ => throw! "unsupported: #unify"
  | Command.compile n => throw! "unsupported: #compile"
  | Command.help n => throw! "unsupported: #help"
  | Command.print (PrintCmd.str s) => pushM `(#print $(Syntax.mkStrLit s))
  | Command.print (PrintCmd.ident n) => do pushM `(#print $(← mkIdentI n.kind))
  | Command.print (PrintCmd.axioms (some n)) => do pushM `(#print axioms $(← mkIdentI n.kind))
  | Command.print _ => throw! "unsupported: advanced #print"
  | Command.userCommand n mods args => throw! "unsupported (TODO): user command {n}"
