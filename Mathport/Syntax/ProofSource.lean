import Mathport.Syntax.Parse
import Mathport.Syntax.Translate

open Mathport
open AST3

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max 
  Level.param Command
open Lean.Elab.Command (CommandElabM liftCoreM)

def proofSource (ast : AST3) : Translate.M (Nat × Lean.Json) := do 
  let prel := ast.«prelude».map fun _ => 
    mkNode ``Parser.Module.prelude #[mkAtom "prelude"]
  let imp ← ast.«import».foldlM (init := #[]) fun imp ns =>
    ns.foldlM (init := imp) fun imp n =>
      return imp.push $ mkNode ``Parser.Module.import #[mkAtom "import",
        mkNullNode, mkIdent (← Translate.renameModule n.kind)]
  let fmt ← liftCoreM $ PrettyPrinter.format Parser.Module.header.formatter $
    mkNode ``Parser.Module.header #[mkOptionalNode prel, mkNullNode imp]
  Translate.printOutput fmt
  let mut currOutput : Substring := (toString (← get).output).toSubstring
  let mut res :  List (String × Lean.Json) := []
  let mut noTheorems := 0
  for command in ast.commands do 
    let kind := command.kind
    if let Command.decl (DeclKind.«theorem») _ (some n) _ _ _ _ _ := kind then 
      noTheorems := noTheorems + 1
      Translate.trCommand command
      let prevOutput := currOutput
      currOutput := (toString (← get).output).toSubstring
      let proofSource := 
        currOutput.extract prevOutput.stopPos currOutput.stopPos
      let thmNameComponents := (← Translate.renameIdent n.kind).componentsRev
      if thmNameComponents.length > 0 then 
        let thmNameStr := toString thmNameComponents.head!
        let proofSourceJson := Lean.toJson $ s!"{proofSource}"
        res := res ++ [(thmNameStr, proofSourceJson)]
  dbg_trace "Theorems: {noTheorems} | Total : {ast.commands.size}"
  return (noTheorems, Lean.Json.mkObj res)

def synportProofSource (config : Config) (path : Path) 
  : Lean.Elab.Command.CommandElabM Nat := do
  let pcfg := config.pathConfig
  let (ast3, _) ← parseAST3 (path.toLean3 pcfg ".ast.json") false
  dbg_trace "path.mod3: {path.mod3}"
  let (noTheorems, ps) ← (proofSource ast3).run 
    ast3.comments ast3.indexed_nota ast3.indexed_cmds config
  IO.FS.writeFile (path.toLean4proofsource pcfg) (Lean.Json.pretty ps)
  return noTheorems
