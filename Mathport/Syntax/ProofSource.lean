import Mathport.Syntax.Parse
import Mathport.Syntax.Translate
open Mathport
open AST3

-- namespace Mathport.AST3

-- mutual

--   partial def Arm.getPremises : Arm → Array Lean.Name 
--     | Arm.mk lhs rhs => lhs.concatMap (Expr.getPremises ∘ Spanned.kind) ++ rhs.kind.getPremises

--   partial def Proof.getPremises : Proof → Array Lean.Name 
--     | Proof.block (Block.mk _ _ _ ts) => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | _ => #[]

--   partial def Tactic.getPremises : Tactic → Array Lean.Name 
--     | Tactic.«;» ts => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | Tactic.«<|>» ts => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | Tactic.«[]» ts => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | Tactic.block (Block.mk _ _ _ ts) => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | Tactic.«by» t => t.kind.getPremises
--     | Tactic.exact_shortcut e => e.kind.getPremises
--     | Tactic.expr e => e.kind.getPremises
--     | Tactic.interactive n params => params.concatMap (Param.getPremises ∘ Spanned.kind)

--   partial def VMCalls.getPremises : VMCall → Array Lean.Name 
--     | VMCall.ident n => #[n]
--     | VMCall.expr e => e.getPremises
--     | VMCall.pat e => e.getPremises
--     | VMCall.block (Block.mk _ _ _ ts) => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | _ => #[]

--   partial def Param.getPremises : Param → Array Lean.Name 
--     | Param.parse e vmcalls => vmcalls.concatMap (VMCalls.getPremises ∘ Spanned.kind)
--     | Param.expr e => e.kind.getPremises
--     | Param.block (Block.mk _ _ _ ts) => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     --| _ => #[]

--   partial def Expr.getPremises : Expr → Array Lean.Name 
--     | Expr.ident n => #[n]
--     | Expr.const n _ es => es.push n.kind
--     | Expr.paren e => e.kind.getPremises
--     | Expr.app e1 e2 => e1.kind.getPremises ++ e2.kind.getPremises
--     | Expr.«fun» _ _ e => e.kind.getPremises
--     | Expr.«→» e1 e2 => e1.kind.getPremises ++ e2.kind.getPremises
--     | Expr.Pi _ e => e.kind.getPremises
--     | Expr.«show» e pf => e.kind.getPremises ++ pf.kind.getPremises
--     | Expr.«have» _ _ e1 pf e2 => e1.kind.getPremises ++ pf.kind.getPremises ++ e2.kind.getPremises
--     | Expr.«.» _ e p => e.kind.getPremises -- ++ p.kind.getPremises
--     | Expr.«if» _ e1 e2 e3 => e1.kind.getPremises ++ e2.kind.getPremises ++ e3.kind.getPremises
--     | Expr.«calc» es => es.concatMap (fun (e1, e2) => e1.kind.getPremises ++ e2.kind.getPremises)
--     | Expr.«@» _ e => e.kind.getPremises
--     | Expr.pattern e => e.kind.getPremises
--     | Expr.«`()» _ _ e => e.kind.getPremises
--     | Expr.«%%» e => e.kind.getPremises
--     | Expr.«`[]» ts => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | Expr.«`» _ n => #[n]
--     | Expr.«⟨⟩» es => es.concatMap (fun e => e.kind.getPremises)
--     | Expr.infix_fn _ (some e) => e.kind.getPremises
--     | Expr.«(,)» es => es.concatMap (fun e => e.kind.getPremises)
--     | Expr.«:» e1 e2 => e1.kind.getPremises ++ e2.kind.getPremises
--     | Expr.hole es => es.concatMap (fun e => e.kind.getPremises)
--     | Expr.«#[]» es => es.concatMap (fun e => e.kind.getPremises)
--     | Expr.«by» t => t.kind.getPremises
--     | Expr.begin (Block.mk _ _ _ ts) => ts.concatMap (Tactic.getPremises ∘ Spanned.kind)
--     | Expr.«let» ds e => e.kind.getPremises
--     | Expr.«match» es (some e) arms => es.concatMap (fun e => e.kind.getPremises) ++ e.kind.getPremises ++ arms.concatMap Arm.getPremises 
--     | Expr.«{,}» es => es.concatMap (fun e => e.kind.getPremises)
--     | Expr.subtype _ _ (some e) e2 => e.kind.getPremises ++ e2.kind.getPremises
--     | Expr.sep _ e1 e2 => e1.kind.getPremises ++ e2.kind.getPremises
--     | Expr.setReplacement e _ => e.kind.getPremises
--     | Expr.«.()» e => e.kind.getPremises
--     | _ => #[]

--   partial def DeclVal.getPremises : DeclVal → Array Lean.Name 
--     | DeclVal.expr e => e.getPremises
--     | DeclVal.eqns arms => arms.concatMap Arm.getPremises

--   partial def Command.getPremises : Command → Lean.Name × Array Lean.Name 
--     | Command.decl (DeclKind.«theorem») _ (some n) _ _ _ val _ => (n.kind, val.kind.getPremises)
--     | _ => (Lean.Name.anonymous, #[])
-- end

-- end Mathport.AST3

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param Command
open Lean.Elab.Command (CommandElabM liftCoreM)

def proofSource (ast : AST3) : Translate.M Lean.Json := do 
  let prel := ast.«prelude».map fun _ => mkNode ``Parser.Module.prelude #[mkAtom "prelude"]
  let imp ← ast.«import».foldlM (init := #[]) fun imp ns =>
    ns.foldlM (init := imp) fun imp n =>
      return imp.push $ mkNode ``Parser.Module.import #[mkAtom "import",
        mkNullNode, mkIdent (← Translate.renameModule n.kind)]
  let fmt ← liftCoreM $ PrettyPrinter.format Parser.Module.header.formatter $
    mkNode ``Parser.Module.header #[mkOptionalNode prel, mkNullNode imp]
  let commitInfo := (← read).config.commitInfo
  Translate.printOutput fmt
  -- commands.forM fun c => do
  --   try trCommand c
  --   catch e =>
  --     let e := s!"error in {(← getEnv).mainModule}: {← e.toMessageData.toString}"
  --     println! e
  --     -- println! (repr c.kind)
  --     printOutput f!"/- {e}\nLean 3 AST:\n{(repr c.kind).group}-/\n\n"
  let mut currOutput : Substring := (toString (← get).output).toSubstring
  let mut res :  List (String × Lean.Json) := []
  for command in ast.commands do 
    if let Command.decl (DeclKind.«theorem») _ (some n) _ _ _ _ _ := command.kind then 
      Translate.trCommand command
      let prevOutput := currOutput
      currOutput := (toString (← get).output).toSubstring
      let proofSource := currOutput.extract prevOutput.stopPos currOutput.stopPos
      --let proofSource := (← get).output
      res := res ++ [(toString (← Translate.renameIdent n.kind), Lean.toJson $ s!"{proofSource}")]
      --IO.eprintln s!"Source for {n.kind}: {proofSource}"
    --modify fun s => { s with output := "" }
    --modify fun s => { s with afterNextCommand := #[] }
  return Lean.Json.mkObj res

def synportProofSource (config : Config) (path : Path) : Lean.Elab.Command.CommandElabM Unit := do
  let pcfg := config.pathConfig
  let (ast3, _) ← parseAST3 (path.toLean3 pcfg ".ast.json") false
  let ps ← (proofSource ast3).run ast3.comments ast3.indexed_nota ast3.indexed_cmds config
  IO.FS.writeFile (path.toLean4proofsource pcfg) (Lean.Json.pretty ps)
