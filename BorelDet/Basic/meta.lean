import Mathlib.Tactic

register_simp_attr simp_lengths
register_simp_attr simp_fixing --seemingly not usable in file where declared
register_simp_attr simp_isPosition

open Lean Meta Elab Tactic Term

section abstract
section
open Expr.FoldConstsImpl
unsafe def fold_univ {α : Type} (f : List Level → α → α) (e : Expr) (acc : α) : FoldM α :=
  let rec visit (e : Expr) (acc : α) : FoldM α := do
    if (← get).visited.contains e then
      return acc
    modify fun s => { s with visited := s.visited.insert e }
    match e with
    | .forallE _ d b _   => visit b (← visit d acc)
    | .lam _ d b _       => visit b (← visit d acc)
    | .mdata _ b         => visit b acc
    | .letE _ t v b _    => visit b (← visit v (← visit t acc))
    | .app f a           => visit a (← visit f acc)
    | .proj _ _ b        => visit b acc
    | .const c us         =>
      if (← get).visitedConsts.contains c then
        return acc
      else
        modify fun s => { s with visitedConsts := s.visitedConsts.insert c };
        return f us acc
    | _ => return acc
  visit e acc

@[inline] unsafe def foldUnsafe_univ {α : Type} (e : Expr) (init : α) (f : List Level → α → α) : α :=
  (fold_univ f e init).run' {}

/-- Apply `f` to every constant occurring in `e` once. -/
@[implemented_by foldUnsafe_univ]
opaque Lean.Expr.foldConsts_univ {α : Type} (e : Expr) (init : α) (f : List Level → α → α) : α := init

def names' : Level → List Name
  | Level.zero => []
  | Level.succ u => names' u
  | Level.max u v => names' u ++ names' v
  | Level.imax u v => names' u ++ names' v
  | Level.param n => [n]
  | Level.mvar _ => panic "mvar" --this occurs in covering_lim
def names (x : List Level) := (x.map names').flatten

def getUsedConstants_univ (e : Expr) : List Name :=
  (e.foldConsts_univ [] fun c cs => (names c) ++ cs).dedup
end

elab "abstract" tacs:ppDedent(tacticSeq) : tactic => do
  if (← getGoals).length = 0 then return
  if (← getGoals).length > 1 then do
    throwError "more than one goal"
  let target ← getMainTarget
  let goal ← getMainGoal
  let newGoal ← mkFreshExprMVar target
  setGoals [newGoal.mvarId!]
  Elab.Tactic.evalTactic tacs
  setGoals [goal]
  let prf ← instantiateMVars newGoal
  let target ← instantiateMVars target
  let mut args := #[]
  for hyp in ← getLCtx do
    if (← exprDependsOn prf hyp.fvarId) ∨ (← exprDependsOn target hyp.fvarId) then
      args := args.push hyp.toExpr
  let univs := (getUsedConstants_univ prf ++ getUsedConstants_univ target).dedup
  let nm := (← getDeclName?).get! ++ `abstract ++ (← mkFreshId)
  let v ←  mkLambdaFVars args prf
  if v.hasLevelMVar then panic "mvar'"
  let lem := ConstantInfo.thmInfo {
    name := nm
    levelParams := univs
    type := ← mkForallFVars args target
    value := v }
  addDecl lem.toDeclaration!
  goal.assign <| mkAppN (mkConst nm <| univs.map Level.param) args
end abstract


section simpAtStar
--modify getNondepPropHyps
def Lean.MVarId.getPropHyps (mvarId : MVarId) : MetaM (Array FVarId) := do
  mvarId.withContext do
  let mut result := #[]
  for ldecl in ← getLCtx do
    if !ldecl.isImplementationDetail && (← isProp ldecl.type) && !ldecl.hasValue then
      result := result.push ldecl.fvarId
  return result
--modify simpLocation
def simpLocationAtStar (ctx : Simp.Context)
  (simprocs : Simp.SimprocsArray)
  (discharge? : Option Simp.Discharge := none) :
  Tactic.TacticM Simp.Stats := do
    Tactic.withMainContext do
      go (← (← Tactic.getMainGoal).getPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) :
    TacticM Simp.Stats := do
    let mvarId ← getMainGoal
    let (result?, stats) ← simpGoal mvarId ctx (simprocs := simprocs)
      (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return stats
--variant of simp at * that also simplifies dependent hypotheses
syntax (name := simpAtStar) "simpAtStar" (Parser.Tactic.config)?
  (Parser.Tactic.discharger)? (&" only")?
  (" [" withoutPosition((Parser.Tactic.simpStar
    <|> Lean.Parser.Tactic.simpErase <|> Parser.Tactic.simpLemma),*,?) "]")? : tactic
@[tactic simpAtStar] def evalSimpAtStar : Tactic :=
  fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocationAtStar ctx simprocs discharge?
  return stats.diag
end simpAtStar
