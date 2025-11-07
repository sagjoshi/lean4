import Lean
import Lean.Parser.Term.Basic
import Lean.Elab.Tactic.Do.LetElim
import Std.Tactic.Do
import Init.Control.OptionCps
import Init.Control.StateCps

open Lean Parser Meta Elab

def ExceptT.runK [Monad m] (x : ExceptT ε m α) (ok : α → m β) (error : ε → m β) : m β :=
  x.run >>= (·.casesOn error ok)

def ExceptT.runCatch [Monad m] (x : ExceptT α m α) : m α :=
  x.runK pure pure

abbrev EarlyReturnT (ρ m α) := ExceptT ρ m α
abbrev EarlyReturnT.return {ρ m α} [Monad m] (r : ρ) : EarlyReturnT ρ m α :=
  throw r
abbrev EarlyReturn.runK {ρ α : Type u} {β : Type v} (x : Except ρ α) (ret : ρ → β) (pure : α → β) : β :=
  x.casesOn ret pure

inductive BreakContinue : Type u where
  | break
  | continue

abbrev BreakT := ExceptT BreakContinue
abbrev BreakT.break {m : Type w → Type x} [Monad m] : BreakT m PUnit := throw .break
abbrev BreakT.continue {m : Type w → Type x} [Monad m] : BreakT m PUnit := throw .continue
abbrev Break.runK {α : Type u} {β : Type v} (x : Except BreakContinue.{u} α) (breakK : Unit → β) (continueK : Unit → β) (successK : α → β) : β :=
  x.casesOn (·.casesOn (breakK ()) (continueK ())) successK

class Foldable (ρ : Type u) (α : outParam (Type v)) extends Membership α ρ where
  foldr {β : Type w} : (α → β → β) → β → ρ → β
  foldrMem {β : Type w} : (xs : ρ) → ((a : α) → a ∈ xs → β → β) → β → β
  foldl {β : Type w} : (β → α → β) → β → ρ → β
  foldlMem {β : Type w} : (xs : ρ) → (β → (a : α) → a ∈ xs → β) → β → β
  foldrEta {β : Type w} {γ : Type x} : (α → (β → γ) → β → γ) → (β → γ) → ρ → β → γ
  foldrMemEta {β : Type w} {γ : Type x} : (xs : ρ) → ((a : α) → a ∈ xs → (β → γ) → β → γ) → (β → γ) → β → γ
  length : ρ → Nat

@[specialize 4 5]
def List.foldrEta (kcons : α → (β → γ) → β → γ) (knil : β → γ) : (l : List α) → (b : β) → γ
  | []    , b => knil b
  | a :: l, b => kcons a (foldrEta kcons knil l) b

instance : Foldable (List α) α where
  foldr := List.foldr
  foldl := List.foldl
  foldlMem xs f z := List.foldl (fun b ⟨a, h⟩ => f b a h) z xs.attach
  foldrMem xs f z := List.foldr (fun ⟨a, h⟩ b => f a h b) z xs.attach
  foldrEta := List.foldrEta
  foldrMemEta xs f z := List.foldrEta (fun ⟨a, h⟩ b => f a h b) z xs.attach
  length := List.length

instance : Foldable (Array α) α where
  foldr := Array.foldr
  foldl := Array.foldl
  foldlMem xs f z := Array.foldl (fun b ⟨a, h⟩ => f b a h) z xs.attach
  foldrMem xs f z := Array.foldr (fun ⟨a, h⟩ b => f a h b) z xs.attach
  foldrEta := Array.foldr
  foldrMemEta xs f z := Array.foldr (fun ⟨a, h⟩ b => f a h b) z xs.attach
  length := Array.size

@[specialize]
def Foldable.toList [Foldable ρ α] : ρ → List α :=
  foldr (fun a acc => a :: acc) []

@[specialize]
def Foldable.foldl' [Foldable ρ α] (f : β → α → β) (init : β) (xs : ρ) : β :=
  foldr (fun a k b => k (f b a)) id xs init

class LawfulFoldable (ρ : Type u) (α : outParam (Type v)) [Foldable ρ α] : Prop where
  -- Unsure whether the following law follows by parametricity.
  foldr_eq_foldr_toList (xs : ρ) (k : α → β → β) (z : β) :
    Foldable.foldr k z xs = List.foldr k z (Foldable.toList xs)
  foldrEta_eq_foldr (xs : ρ) (kcons : α → (β → γ) → β → γ) (knil : β → γ) (z : β) :
    Foldable.foldrEta kcons knil xs z = Foldable.foldr kcons knil xs z

@[specialize]
def Foldable.toArray [Foldable ρ α] (xs : ρ) : Array α :=
  foldr (fun a k arr => k (arr.push a)) id xs (Array.mkEmpty (Foldable.length xs))

@[specialize 4 5]
def Foldable.foldrTR [Foldable ρ α] (f : α → β → β) (init : β) (xs : ρ) : β :=
  xs |> Foldable.toArray |>.foldr f init

-- def warmup := Foldable.toArray [3]
-- set_option trace.Compiler.saveBase true in
-- def blah := Foldable.foldrTR (fun a b => a * b) 0 [1, 2, 3]
-- set_option trace.Compiler.saveBase true in
-- example := List.foldr (fun a b => a * b) 0 [1, 2, 3]

set_option pp.all true in
@[inline]
def Foldable.foldrEtaInv {ρ : Type u} {α : Type v} [Foldable ρ α] {m : Type (max v w) → Type x} [Monad m] {σ γ}
    (kcons : α → (σ → m γ) → σ → m γ) (knil : σ → m γ) (xs : ρ) (s : σ)
    [inst : Foldable.{u,v,v,v} ρ α] {ps} [Std.Do.WP m ps] (inv : Std.Do.Invariant (inst.toList xs) σ ps) : m γ :=
  Foldable.foldrEta kcons knil xs s

declare_syntax_cat dooElem

meta def dooElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `dooElem rbp

meta def dooSeqItem      := leading_parser
  ppLine >> dooElemParser >> optional "; "
meta def dooSeqIndent    := leading_parser
  many1Indent dooSeqItem
meta def dooSeqBracketed := leading_parser
  "{" >> withoutPosition (many1 dooSeqItem) >> ppLine >> "}"
meta def dooSeq :=
  withAntiquot (mkAntiquot "dooSeq" decl_name% (isPseudoKind := true)) <|
    dooSeqBracketed <|> dooSeqIndent
meta def dooIdDecl := leading_parser
  atomic (ident >> Term.optType >> ppSpace >> Term.leftArrow) >>
  dooElemParser
syntax:arg (name := dooBlock) "doo" dooSeq : term

-- syntax (name := dooTerm) Term.doExpr : dooElem
abbrev dooTerm := Term.doExpr
attribute [dooElem_parser] dooTerm
syntax (name := dooParens) "(" dooSeq ")" : dooElem
syntax (name := dooReturn) &"return " term : dooElem
syntax (name := dooBreak) &"break" : dooElem
syntax (name := dooContinue) &"continue" : dooElem
syntax (name := dooLet) "let " &"mut "? letDecl : dooElem
syntax (name := dooLetArrow) "let " &"mut "? dooIdDecl : dooElem
syntax (name := dooNested) "doo" dooSeq : dooElem
meta def dooForDecl := leading_parser
  termParser >> " in " >> withForbidden "doo" termParser
syntax (name := dooFor) "for " dooForDecl,+ "doo " dooSeq : dooElem
syntax (name := dooCatch) ppDedent(ppLine) atomic("catch " binderIdent) Term.optType " => " dooSeq : dooElem
syntax (name := dooFinally) ppDedent(ppLine) "finally " dooSeq : dooElem
syntax (name := dooTry) "try " dooSeq (dooCatch)* (dooFinally)? : dooElem
-- def dooCatch      := leading_parser
--   ppDedent ppLine >> atomic ("catch " >> Term.binderIdent) >> optional (" : " >> termParser) >> darrow >> dooSeq
-- def dooFinally    := leading_parser
--   ppDedent ppLine >> "finally " >> dooSeq
-- @[dooElem_parser] def dooTry    := leading_parser
--   "try " >> dooSeq >> many dooCatch >> optional dooFinally

meta def dooInvariant := leading_parser
  "invariant " >> withPosition (
    ppGroup (many1 (ppSpace >> termParser argPrec) >> unicodeSymbol " ↦" " =>" (preserveForPP := true)) >> ppSpace >> withForbidden "doo" termParser)
syntax (name := dooForInvariant) "for " dooForDecl ppSpace dooInvariant "doo " dooSeq : dooElem

@[dooElem_parser]
meta def dooReassign      := leading_parser
  Term.notFollowedByRedefinedTermToken >> Term.letIdDeclNoBinders

@[dooElem_parser]
meta def dooReassignArrow := leading_parser
  Term.notFollowedByRedefinedTermToken >> dooIdDecl

@[dooElem_parser]
meta def dooIf := leading_parser withResetCache <| withPositionAfterLinebreak <| ppRealGroup <|
  -- ppRealFill (ppIndent ("if " >> doIfCond >> " then") >> ppSpace >> doSeq) >>
  ppRealFill (ppIndent ("if " >> termParser >> " then") >> ppSpace >> dooSeq) >>
  many (checkColGe "'else if' in 'do' must be indented" >>
    -- group (ppDedent ppSpace >> ppRealFill (elseIf >> doIfCond >> " then " >> doSeq))) >>
    group (ppDedent ppSpace >> ppRealFill (Term.elseIf >> termParser >> " then " >> dooSeq))) >>
  optional (checkColGe "'else' in 'do' must be indented" >>
    ppDedent ppSpace >> ppRealFill ("else " >> dooSeq))

meta def getDooElems (dooSeq : TSyntax `dooSeq) : Array (TSyntax `dooElem) :=
  if dooSeq.raw.getKind == ``dooSeqBracketed then
    dooSeq.raw[1].getArgs.map fun arg => ⟨arg[0]⟩
  else if dooSeq.raw.getKind == ``dooSeqIndent then
    dooSeq.raw[0].getArgs.map fun arg => ⟨arg[0]⟩
  else
    #[]

namespace Do

structure MonadInfo where
  /-- The inferred type of the monad of type `Type u → Type v`. -/
  m : Expr
  /-- The `u` in `m : Type u → Type v`. -/
  u : Level
  /-- The `v` in `m : Type u → Type v`. -/
  v : Level
  /-- The cached `PUnit` expression. -/
  cachedPUnit : Expr :=
    if u matches .zero then mkConst ``Unit else mkConst ``PUnit [mkLevelSucc u]
  /-- The cached `PUnit.unit` expression. -/
  cachedPUnitUnit : Expr :=
    if u matches .zero then mkConst ``Unit.unit else mkConst ``PUnit.unit [mkLevelSucc u]

/-- Extracts `MonadInfo` and monadic result type `α` from the expected type of a `do` block `m α`. -/
private meta partial def extractMonadInfo (expectedType? : Option Expr) : TermElabM (MonadInfo × Expr) := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let extractStep? (type : Expr) : TermElabM (Option (MonadInfo × Expr)) := do
    let .app m resultType := type.consumeMData | return none
    unless ← isType resultType do return none
    let .succ u ← getLevel resultType | return none
    let .succ v ← getLevel type | return none
    let u := u.normalize
    let v := v.normalize
    return some ({ m, u, v }, resultType)
  let rec extract? (type : Expr) : TermElabM (Option (MonadInfo × Expr)) := do
    match (← extractStep? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        -- Term.tryPostponeIfMVar typeNew.getAppFn
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `do` notation, expected type is not a monad application{indentExpr expectedType}\nYou can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad."
where
  mkUnknownMonadResult : TermElabM (MonadInfo × Expr) := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let m ← mkFreshExprMVar (← mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v))) (userName := `m)
    let resultType ← mkFreshExprMVar (mkSort (mkLevelSucc u)) (userName := `α)
    return ({ m, u, v }, resultType)

-- Same pattern as for `Methods`/`MethodsRef` in `SimpM`.
private opaque ContInfoRefPointed : NonemptyType.{0}

def ContInfoRef : Type := ContInfoRefPointed.type

instance : Nonempty ContInfoRef :=
  by exact ContInfoRefPointed.property

structure Context where
  /-- Inferred and cached information about the monad. -/
  monadInfo : MonadInfo
  /-- The mutable variables in declaration order. -/
  mutVars : Array Name := #[]
  /--
  The expected type of the current `do` block.
  This can be different from `earlyReturnType` in `for` loop `do` blocks, for example.
  -/
  doBlockResultType : Expr
  contInfo : ContInfoRef

structure MonadInstanceCache where
  /-- The inferred `Pure` instance of `(← read).monadInfo.m`. -/
  instPure : Option Expr := none
  /-- The inferred `Bind` instance of `(← read).monadInfo.m`. -/
  instBind : Option Expr := none
  /-- The cached `Pure.pure` expression. -/
  cachedPure : Option Expr := none
  /-- The cached `Bind.bind` expression. -/
  cachedBind : Option Expr := none

/--
A continuation metavariable.

When generating jumps to join points or filling in expressions for `break` or `continue`, it is
still unclear what mutable variables need to be passed, because it depends on which mutable
variables were reassigned in the control flow path to *any* of the jumps.

The mechanism of `ContVarId` allows to delay the assignment of the jump expressions until the local
contexts of all the jumps are known.
-/
structure ContVarId where
  name : Name
  deriving Inhabited, BEq, Hashable

/--
Information about a jump site associated to `ContVarId`.
There will be one instance per jump site to a join point, or for each `break` or `continue`
element.
-/
structure ContVarJump where
  /--
  The metavariable to be assigned with the jump to the join point.
  Conveniently, its captured local context is that of the jump, in which the new mutable variable
  definitions and result variable are in scope.
  -/
  mvar : Expr
  lctx : LocalContext
  /-- A reference for error reporting. -/
  ref : Syntax

/--
Information about a `ContVarId`.
-/
structure ContVarInfo where
  /-- The monadic type of the continuation. -/
  type : Expr
  /--
  A superset of the local variable names that the jumps will refer to. Often the `mut` variables.
  Any `let`-bound FV will be turned into a `have`-bound FV by setting their `nondep` flag in the
  local context of the metavariable for the jump site. This is a technicality to ensure that
  `isDefEq` will not inline the `let`s.
  -/
  tunneledVars : Std.HashSet Name
  /-- Local context at the time the continuation variable was created. -/
  lctx : LocalContext
  /-- The tracked jumps to the continuation. Each contains a metavariable to be assigned later. -/
  jumps : Array ContVarJump

structure State where
  monadInstanceCache : MonadInstanceCache := {}
  contVars : Std.HashMap ContVarId ContVarInfo := {}

abbrev DoElabM := ReaderT Context <| StateRefT State TermElabM

/--
Elaboration of a `do` block `do $e; $rest`, results in a call
``elabTerm `(do $e; $rest) = elabElem e dec``, where `elabElem e ·` is the elaborator for `do`
element `e`, and `dec` is the `DoElemCont` describing the elaboration of the rest of the block
`rest`.

If the semantics of `e` resumes its continuation `rest`, its elaborator must bind its result to
`resultName`, ensure that it has type `resultType` and then elaborate `rest` using `dec`.

Clearly, for term elements `e : m α`, the result has type `α`.
More subtly, for binding elements `let x := e` or `let x ← e`, the result has type `PUnit` and is
unrelated to the type of the bound variable `x`.

Examples:
* `return` drops the continuation; `return x; pure ()` elaborates to `pure x`.
* `let x ← e; rest x` elaborates to `e >>= fun x => rest x`.
* `let x := 3; let y ← (let x ← e); rest x` elaborates to
  `let x := 3; e >>= fun x_1 => let y := (); rest x`, which is immediately zeta-reduced to
  `let x := 3; e >>= fun x_1 => rest x`.
* `one; two` elaborates to `one >>= fun (_ : PUnit) => two`; it is an error if `one` does not have
  type `PUnit`.
-/
structure DoElemCont where
  /-- The name of the monadic result variable. -/
  resultName : Name
  /-- The type of the monadic result. -/
  resultType : Expr
  /-- The continuation to elaborate the `rest` of the block. -/
  k : DoElabM Expr
deriving Inhabited

/--
The type of elaborators for `do` block elements.

It is ``elabTerm `(do $e; $rest) = elabElem e dec``, where `elabElem e ·` is the elaborator for `do`
element `e`, and `dec` is the `DoElemCont` describing the elaboration of the rest of the block
`rest`.
-/
abbrev DoElemElab := DoElemCont → DoElabM Expr

/--
Information about a success, `return`, `break` or `continue` continuation that will be filled in
after the code using it has been elaborated.
-/
structure ContInfo where
  returnCont : DoElemCont
  breakCont : Option (DoElabM Expr) := none
  continueCont : Option (DoElabM Expr) := none
deriving Inhabited

unsafe def ContInfo.toContInfoRefImpl (m : ContInfo) : ContInfoRef :=
  unsafeCast m

@[implemented_by ContInfo.toContInfoRefImpl]
opaque ContInfo.toContInfoRef (m : ContInfo) : ContInfoRef

unsafe def ContInfoRef.toContInfoImpl (m : ContInfoRef) : ContInfo :=
  unsafeCast m

@[implemented_by ContInfoRef.toContInfoImpl]
opaque ContInfoRef.toContInfo (m : ContInfoRef) : ContInfo

/-- Constructs `m α` from `α`. -/
meta def mkMonadicType (resultType : Expr) : DoElabM Expr := do
  return mkApp (← read).monadInfo.m resultType

/-- The cached `PUnit` expression. -/
meta def mkPUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnit

/-- The cached ``PUnit.unit`` expression. -/
meta def mkPUnitUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnitUnit

/-- The cached `@Pure.pure m instPure` expression. -/
meta def getCachedPure : DoElabM Expr := do
  let s ← get
  if let some cachedPure := s.monadInstanceCache.cachedPure then return cachedPure
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Pure [info.u, info.v]) info.m)
  let cachedPure := mkApp2 (mkConst ``Pure.pure [info.u, info.v]) info.m instPure
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedPure := some cachedPure } : State}
  return cachedPure

/-- The expression ``pure (α:=α) e``. -/
meta def mkPureApp (α e : Expr) : DoElabM Expr := do
  let e ← Term.ensureHasType α e
  return mkApp2 (← getCachedPure) α e

/-- Create a `DoElemCont` returning the result using `pure`. -/
meta def DoElemCont.mkPure (resultType : Expr) : TermElabM DoElemCont := do
  let r ← mkFreshUserName `r
  return { resultName := r, resultType, k := do mkPureApp resultType (← getFVarFromUserName r) }

/-- Create the `Context` for `do` elaboration from the given expected type of a `do` block. -/
meta def mkContext (expectedType? : Option Expr) : TermElabM Context := do
  let (mi, resultType) ← extractMonadInfo expectedType?
  let returnCont ← DoElemCont.mkPure resultType
  let contInfo := ContInfo.toContInfoRef { returnCont }
  return { monadInfo := mi, doBlockResultType := resultType, contInfo }

/-- The cached `@Bind.bind m instBind` expression. -/
meta def getCachedBind : DoElabM Expr := do
  let s ← get
  if let some cachedBind := s.monadInstanceCache.cachedBind then return cachedBind
  let info := (← read).monadInfo
  let instBind ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  let cachedBind := mkApp2 (mkConst ``Bind.bind [info.u, info.v]) info.m instBind
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedBind := some cachedBind } : State}
  return cachedBind

/-- The expression ``Bind.bind (α:=α) (β:=β) e k``. -/
meta def mkBindApp (α β e k : Expr) : DoElabM Expr := do
  let mα ← mkMonadicType α
  let e ← Term.ensureHasType mα e
  let k ← Term.ensureHasType (← mkArrow α (← mkMonadicType β)) k
  let cachedBind ← getCachedBind
  return mkApp4 cachedBind α β e k

/-- Register the given name as that of a `mut` variable. -/
meta def declareMutVar (x : Name) : DoElabM α → DoElabM α :=
  withReader fun ctx => { ctx with mutVars := ctx.mutVars.push x }

/-- Register the given name as that of a `mut` variable if the syntax token `mut` is present. -/
meta def declareMutVar? (mutTk? : Option Syntax) (x : Name) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVar x k else k

/-- Throw an error if the given name is not a declared `mut` variable. -/
meta def throwUnlessMutVarDeclared (x : Name) : DoElabM Unit := do
  unless (← read).mutVars.contains x do
    throwError "undeclared mutable variable `{x}`"

/-- Throw an error if a declaration of the given name would shadow a `mut` variable. -/
meta def checkMutVarsForShadowing (x : Name) : DoElabM Unit := do
  if (← read).mutVars.contains x then
    throwError "mutable variable `{x.simpMacroScopes}` cannot be shadowed"

/-- Create a fresh `α` that would fit in `m α`. -/
meta def mkFreshResultType (userName := `α) : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := userName)

meta def synthUsingDefEq (msg : String) (expected : Expr) (actual : Expr) : DoElabM Unit := do
  unless ← isDefEq expected actual do
    throwError "Failed to synthesize {msg}. {expected} is not definitionally equal to {actual}."

/--
Has the effect of ``e >>= fun (x : eResultTy) => $(← k `(x))``.
Ensures that `e` has type `m eResultTy`.
-/
meta def mkBindCancellingPure (x : Name) (eResultTy e : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  withLocalDeclD x eResultTy fun x => do
    let body ← k x
    let body' := body.consumeMData
    if body'.isAppOfArity ``Pure.pure 4 && body'.getArg! 3 == x then
      return e
    let kResultTy ← mkFreshResultType `kResultTy
    let k ← mkLambdaFVars #[x] body
    mkBindApp eResultTy kResultTy e k

/--
A variant of `Term.elabType` that takes the universe of the monad into account, unless
`freshLevel` is set.
-/
meta def elabType (ty? : Option (TSyntax `term)) (freshLevel := false) : DoElabM Expr := do
  let u ← if freshLevel then mkFreshLevelMVar else (mkLevelSucc ·.monadInfo.u) <$> read
  let sort := mkSort u
  match ty? with
  | none => mkFreshExprMVar sort
  | some ty => Term.elabTermEnsuringType ty sort

meta def elabBinder (binder : Syntax) (x : Expr → DoElabM α) : DoElabM α := do
  controlAt TermElabM fun runInBase => Term.elabBinder binder (runInBase ∘ x)

/--
Batched version of `Lean.LocalContext.findFromUserName?`.
Finds the reaching definitions for each of the given `userNames` up to a certain `start` index, if any.
-/
meta def _root_.Lean.LocalContext.findFromUserNames (lctx : LocalContext) (userNames : Std.HashSet Name) (start := 0) : Array LocalDecl :=
  Array.reverse <| Id.run <| ExceptT.runCatch do
    let (_, _, acc) ← lctx.foldrM (init := (userNames, lctx.numIndices - 1, #[])) fun decl (userNames, i, acc) => do
      if userNames.isEmpty then throw acc -- stop when we found all user names
      if i < start then throw acc         -- stop when we reached the start index
      if userNames.contains decl.userName then
        pure (userNames.erase decl.userName, i - 1, acc.push decl)
      else
        pure (userNames, i - 1, acc)
    return acc.reverse

/--
The subset of `mutVars` that were reassigned in any of the `childCtxs` relative to the given
`rootCtx`.
-/
meta def _root_.Lean.LocalContext.getReassignedMutVars (rootCtx : LocalContext) (mutVars : Std.HashSet Name) (childCtxs : Array LocalContext) : Std.HashSet Name := Id.run do
  let mut reassignedMutVars := Std.HashSet.emptyWithCapacity mutVars.size
  for childCtx in childCtxs do
    let newDefs := childCtx.findFromUserNames mutVars (start := rootCtx.numIndices)
    reassignedMutVars := reassignedMutVars.insertMany (newDefs.map (·.userName))
  return reassignedMutVars

/--
Adds the new reaching definitions of the given `tunneledVars` in `childCtx` relative to `rootCtx` as
non-dependent decls.
-/
meta def _root_.Lean.LocalContext.addNewVarDefsAsNonDep (rootCtx childCtx : LocalContext) (tunneledVars : Std.HashSet Name) : LocalContext := Id.run do
  let tunnelDecls := childCtx.findFromUserNames tunneledVars (start := rootCtx.numIndices)
  let mut rootCtx := rootCtx
  for decl in tunnelDecls do
    rootCtx := rootCtx.addDecl (decl.setNondep true)
  return rootCtx

/--
Creates a new continuation variable of type `m α` given the result type `α`.
The `tunneledVars` is a superset of the `let`-bound variable names that the jumps will refer to.
Often it will be the `mut` variables. Leaving it empty inlines `let`-bound variables at jump sites.
-/
meta def mkFreshContVar (resultType : Expr) (tunneledVars : Array Name) : DoElabM ContVarId := do
  let name ← mkFreshId
  let contVarId := ContVarId.mk name
  let type ← mkMonadicType resultType
  let tunneledVars := Std.HashSet.ofArray tunneledVars
  let cvInfo := { type, jumps := #[], lctx := (← getLCtx), tunneledVars }
  modify fun s => { s with contVars := s.contVars.insert contVarId cvInfo }
  return contVarId

meta def ContVarId.find (contVarId : ContVarId) : DoElabM ContVarInfo := do
  match (← get).contVars.get? contVarId with
  | some info => return info
  | none => throwError "contVarId {contVarId.name} not found"

/-- Creates a new jump site for the continuation variable, to be synthesized later. -/
meta def ContVarId.mkJump (contVarId : ContVarId) : DoElabM Expr := do
  let info ← contVarId.find
  let lctx := info.lctx.addNewVarDefsAsNonDep (← getLCtx) info.tunneledVars
  let mvar ← withLCtx' lctx (mkFreshExprMVar info.type)
  let jumps := info.jumps.push { mvar, lctx, ref := (← getRef) }
  modify fun s => { s with contVars := s.contVars.insert contVarId { info with jumps } }
  return mvar

/-- The number of jump sites allocated for the continuation variable. -/
meta def ContVarId.jumpCount (contVarId : ContVarId) : DoElabM Nat := do
  let info ← contVarId.find
  return info.jumps.size

/--
Synthesize the jump sites for the continuation variable.
`k` is run once for each jump site, in the `LocalContext` of the jump site.
The result of `k` is used to fill in the jump site.
-/
meta def ContVarId.synthesizeJumps (contVarId : ContVarId) (k : DoElabM Expr) : DoElabM Unit := do
  let info ← contVarId.find
  for jump in info.jumps do
    withLCtx' jump.lctx do withRef jump.ref do
      let res ← k
      let mvar := (← instantiateMVars jump.mvar).getAppFn.mvarId!
      let head := (← instantiateMVars res).getAppFn
      if head.isMVar then
        trace[Elab.do] "Assigning jump site {mvar} with {head.mvarId!}"
      fullApproxDefEq <| synthUsingDefEq "jump site" jump.mvar res

meta def ContVarId.erase (contVarId : ContVarId) : DoElabM Unit := do
  modify fun s => { s with contVars := s.contVars.erase contVarId }

/--
The subset of `(← read).mutVars` that were reassigned at any of the jump sites of the continuation
variable. The result array has the same order as `(← read).mutVars`.
-/
meta def ContVarId.getReassignedMutVars (contVarId : ContVarId) (rootCtx : LocalContext) : DoElabM (Std.HashSet Name) := do
  let info ← contVarId.find
  let childCtxs ← info.jumps.mapM fun j => return (← j.mvar.mvarId!.getDecl).lctx
  return rootCtx.getReassignedMutVars (.ofArray (← read).mutVars) childCtxs

/--
Restores the local context to `oldCtx` and adds the new reaching definitions of the mut vars and
result. Then resume the continuation `k` with the `mutVars` restored to the given `oldMutVars`.

This function is useful to de-nest
```
let mut x := 0
let y := 3
let z ← do
  let mut y ← e
  x := y + 1
  pure y
let y := y + 3
pure (x + y + z)
```
into
```
let mut x := 0
let y := 3
let mut y† ← e
x := y† + 1
let z ← pure y†
let y := y + 3
pure (x + y + z)
```
Note that the continuation of the `let z ← ...` bind, roughly
``k := .cont `z _ `(let y := y + 3; pure (x + y + z))``,
needs to elaborated in a local context that contains the reassignment of `x`, but not the shadowing
mut var definition of `y`.
-/
meta def withLCtxKeepingMutVarDefs (oldCtx : LocalContext) (oldMutVars : Array Name) (resultName : Name) (k : DoElabM α) : DoElabM α := do
  let newCtx := oldCtx.addNewVarDefsAsNonDep (← getLCtx) (.ofArray <| oldMutVars.push resultName)
  withLCtx' newCtx <| withReader (fun ctx => { ctx with mutVars := oldMutVars }) k

/--
Return `$e >>= fun ($dec.resultName : $dec.resultType) => $(← dec.k)`, cancelling
the bind if `$(← dec.k)` is `pure $dec.resultName`.
-/
meta def DoElemCont.mkBindUnlessPure (dec : DoElemCont) (e : Expr) : DoElabM Expr := do
  mkBindCancellingPure dec.resultName dec.resultType e (fun _ => dec.k)

/-- Has the effect of ``let x : ty := rhs; $(← k `(x))`` and then zeta-reducing the expression. -/
meta def mapLetDeclZeta (name : Name) (type rhs : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  withLetDecl name type rhs fun x => do
    let e ← k x
    let e ← elimMVarDeps #[x] e
    return e.replaceFVar x rhs

/--
Return `let $k.resultName : PUnit := PUnit.unit; $(← k.k)`, ensuring that the result type of `k.k`
is `PUnit` and then immediately zeta-reduce the `let`.
-/
meta def DoElemCont.continueWithUnit (dec : DoElemCont) : DoElabM Expr := do
  let unit ← mkPUnitUnit
  discard <| Term.ensureHasType dec.resultType unit
  mapLetDeclZeta dec.resultName (← mkPUnit) unit (fun _ => dec.k)

/--
Call `caller` with a duplicable proxy of `dec`.
When the proxy is elaborated more than once, a join point is introduced so that `dec` is only
elaborated once to fill in the RHS of this join point.

This is useful for control-flow constructs like `if` and `match`, where multiple tail-called
branches share the continuation.
-/
meta def DoElemCont.withDuplicableCont (nondupDec : DoElemCont) (caller : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  let α := (← read).doBlockResultType
  let mα ← mkMonadicType α
  let joinTy ← mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.v)) (userName := `joinTy)
  let joinRhs ← mkFreshExprMVar joinTy (userName := `joinRhs)
  withLetDecl (← mkFreshUserName `__do_jp) joinTy joinRhs (kind := .implDetail) (nondep := true) fun jp => do
    let mutVars := (← read).mutVars
    let contVarId ← mkFreshContVar α (mutVars.push nondupDec.resultName)
    let duplicableDec := { nondupDec with k := contVarId.mkJump }
    let e ← caller duplicableDec

    -- Now determine whether we need to realize the join point.
    let jumpCount ← contVarId.jumpCount
    if jumpCount = 0 then
      -- Do nothing. No MVar needs to be assigned.
      Term.ensureHasType mα e
    else if jumpCount = 1 then
      -- Linear use of the continuation. Do not introduce a join point; just emit the continuation
      -- directly.
      contVarId.synthesizeJumps nondupDec.k
      let e ← Term.ensureHasType mα e
      -- Now zeta-reduce `jp`. Should be a semantic no-op.
      let e ← elimMVarDeps #[jp] e
      return e.replaceFVar jp joinRhs
    else -- jumps.size > 1
      -- Non-linear use of the continuation. Introduce a join point and synthesize jumps to it.

      -- Compute the union of all reassigned mut vars. These + `r` constitute the parameters
      -- of the join point. We take a little care to preserve the declaration order that is manifest
      -- in the array `(← read).mutVars`.
      let reassignedMutVars ← contVarId.getReassignedMutVars (← joinRhs.mvarId!.getDecl).lctx
      let reassignedMutVars := mutVars.filter reassignedMutVars.contains

      -- Assign the `joinTy` based on the types of the reassigned mut vars and the result type.
      let reassignedDecls ← reassignedMutVars.mapM (getLocalDeclFromUserName ·)
      let reassignedTys := reassignedDecls.map (·.type)
      let resTy ← mkFreshResultType
      let joinTy' ← mkArrowN (reassignedTys.push resTy) mα
      synthUsingDefEq "join point type" joinTy joinTy'

      -- Assign the `joinRhs` with the result of the continuation.
      let rhs ← joinRhs.mvarId!.withContext do
        withLocalDeclsDND (reassignedDecls.map (fun d => (d.userName, d.type)) |>.push (nondupDec.resultName, resTy)) fun xs => do
          mkLambdaFVars xs (← nondupDec.k)
      synthUsingDefEq "join point RHS" joinRhs rhs

      -- Finally, assign the MVars with the jump to `jp`.
      contVarId.synthesizeJumps do
        let r ← getFVarFromUserName nondupDec.resultName
        let mut jump := jp
        for name in reassignedMutVars do
          let newDefn ← getLocalDeclFromUserName name
          jump := mkApp jump newDefn.toExpr
        return mkApp jump (← Term.ensureHasType resTy r "Mismatched result type for match arm. It")

      mkLetFVars #[jp] (generalizeNondepLet := false) (← Term.ensureHasType mα e)

/-- Given types `tᵢ`, return the tuple type `t₁ × t₂ × … × tₙ`. -/
meta def mkProdN (ts : Array Expr) : MetaM Expr := do
  if h : ts.size > 0 then
    let mut tupleTy := ts.back
    let mut u ← getDecLevel tupleTy
    let mut ts := ts.pop
    for i in 0...ts.size do
      let ty := ts.back!
      let u' ← getDecLevel ty
      tupleTy := mkApp2 (mkConst ``Prod [u', u]) ty tupleTy
      u := (mkLevelMax u u').normalize
      ts := ts.pop
    return tupleTy
  else
    let u ← mkFreshLevelMVar
    return mkConst ``PUnit [u]

/-- Given expressions `eᵢ`, return the tuple `(e₁, e₂, …, eₙ)` and its type `t₁ × t₂ × … × tₙ`. -/
meta def mkProdMkN (es : Array Expr) : MetaM (Expr × Expr) := do
  if h : es.size > 0 then
    let mut tuple := es.back
    let mut tupleTy ← inferType tuple
    let mut u ← getDecLevel tupleTy
    let mut es := es.pop
    for i in 0...es.size do
      let e := es.back!
      let ty ← inferType e
      let u' ← getDecLevel ty
      tuple := mkApp4 (mkConst ``Prod.mk [u', u]) ty tupleTy e tuple
      tupleTy := mkApp2 (mkConst ``Prod [u', u]) ty tupleTy
      u := (mkLevelMax u u').normalize
      es := es.pop
    return (tuple, tupleTy)
  else
    let u ← mkFreshLevelMVar
    return (mkConst ``PUnit.unit [u], mkConst ``PUnit [u])

/-- Given a product `(e₁, e₂)` of type `t₁ × t₂`, return `(e₁, t₁, e₂, t₂)`. -/
meta def getProdFields (tuple tupleTy : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let tupleTy ← instantiateMVarsIfMVarApp tupleTy
  let_expr c@Prod fstTy sndTy := tupleTy
    | throwError "Internal error: Expected Prod, got {tuple} of type {tupleTy}"
  let fst := mkApp3 (mkConst ``Prod.fst c.constLevels!) fstTy sndTy tuple
  let snd := mkApp3 (mkConst ``Prod.snd c.constLevels!) fstTy sndTy tuple
  return (fst, fstTy, snd, sndTy)

/--
Given a list of mut vars `vars` and an FVar `tupleVar` binding a tuple, bind the mut vars to the
fields of the tuple and call `k` in the resulting local context.
-/
meta def bindMutVarsFromTuple (vars : List Name) (tupleVar : FVarId) (k : DoElabM Expr) : DoElabM Expr :=
  do go vars tupleVar (← tupleVar.getType) #[]
where
  go vars tupleVar tupleTy letFVars := do
    let tuple := mkFVar tupleVar
    match vars with
    | []  => mkLetFVars letFVars (← k)
    | [x] =>
      withLetDecl x tupleTy tuple fun x => do mkLetFVars (letFVars.push x) (← k)
    | [x, y] =>
      let (fst, fstTy, snd, sndTy) ← getProdFields tuple tupleTy
      withLetDecl x fstTy fst fun x =>
      withLetDecl y sndTy snd fun y => do mkLetFVars (letFVars.push x |>.push y) (← k)
    | x :: xs => do
      let (fst, fstTy, snd, sndTy) ← getProdFields tuple tupleTy
      withLetDecl x fstTy fst fun x => do
      withLetDecl (← tupleVar.getUserName) sndTy snd fun r => do
        go xs r.fvarId! sndTy (letFVars |>.push x |>.push r)

meta def getReturnCont : DoElabM DoElemCont := do
  return (← read).contInfo.toContInfo.returnCont

meta def getBreakCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.breakCont

meta def getContinueCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.continueCont

/--
Prepare the context for elaborating the body of a loop.
This includes setting the return continuation, break continuation, continue continuation, as
well as the changed result type of the `do` block in the loop body.
-/
meta def enterLoopBody (resultType : Expr) (returnCont : DoElemCont) (breakCont continueCont : DoElabM Expr) : (body : DoElabM α) → DoElabM α :=
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  withReader fun ctx => { ctx with contInfo, doBlockResultType := resultType }

/--
Prepare the context for elaborating the body of a `do` block that does not support `mut` vars,
`break`, `continue` or `return`.
-/
meta def withoutControl (k : DoElabM Expr) : DoElabM Expr := do
  let error := throwError "This `do` block does not support `break`, `continue` or `return`."
  let dec ← getReturnCont
  let contInfo := { breakCont := error, continueCont := error, returnCont := { dec with k := error }}
  let contInfo := ContInfo.toContInfoRef contInfo
  withReader (fun ctx => { ctx with contInfo }) k

/--
Prepare the context for elaborating the body of a `finally` block.
There is no support for `mut` vars, `break`, `continue` or `return` in a `finally` block.
-/
meta def enterFinally (resultType : Expr) (k : DoElabM Expr) : DoElabM Expr := do
  withoutControl do
  withReader (fun ctx => { ctx with doBlockResultType := resultType }) k

structure ControlStack where
  monadInfo : MonadInfo
  instMonad : Expr
  stM : Expr → Expr
  runInBase : Expr → DoElabM Expr
  restoreCont : DoElemCont → MetaM DoElemCont

def ControlStack.base (mi : MonadInfo) (instMonad : Expr) : ControlStack where
  monadInfo := mi
  instMonad := instMonad
  stM α := α
  runInBase e := pure e
  restoreCont dec := pure dec

def ControlStack.stateT (reassignedMutVars : Array Name) (σ : Expr) (m : ControlStack) : ControlStack where
  monadInfo :=
    { mi with m := mkApp2 (mkConst ``StateT [mi.u, mi.v]) σ mi.m }
  instMonad :=
    mkApp3 (mkConst ``StateT.instMonad [mi.u, mi.v]) σ mi.m m.instMonad
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : StateT σ m α`. Fetch the state tuple `s : σ` and apply it to `e`, `e.run s`.
    -- See also `StateT.monadControl.liftWith`.
    let (tuple, _tupleTy) ← mkProdMkN (← reassignedMutVars.mapM (getFVarFromUserName ·))
    let tuple ← Term.ensureHasType σ tuple
    return mkApp e tuple
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `(dec.resultType × σ)` by unpacking the state tuple
    -- before calling `dec.k`. See also `StateT.monadControl.restoreM`.
    let resultName ← mkFreshUserName `p
    let resultType := stM dec.resultType
    let k := do
      let p ← getFVarFromUserName resultName
      bindMutVarsFromTuple (dec.resultName :: reassignedMutVars.toList) p.fvarId! do
        dec.k
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp2 (mkConst ``Prod [mi.u, mi.u]) α σ

def ControlStack.earlyReturnT (ρ : Expr) (m : ControlStack) : ControlStack where
  monadInfo :=
    { mi with m := mkApp2 (mkConst ``EarlyReturnT [mi.u, mi.v]) ρ mi.m }
  instMonad :=
    mkApp3 (mkConst ``ExceptT.instMonad [mi.u, mi.v]) ρ mi.m m.instMonad
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : EarlyReturnT ρ m α`. Return `e`, which is defeq to `ExceptT.run e`.
    -- See also `instMonadControlExceptTOfMonad.liftWith`.
    return e
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `Except ρ dec.resultType` by unpacking the exception,
    -- calling `dec.k` in the success case. See also `instMonadControlExceptTOfMonad.restoreM`.
    let resultName ← mkFreshUserName `e
    let resultType := stM dec.resultType
    let k := do
      let e ← getFVarFromUserName resultName
      let outerReturnCont ← getReturnCont
      let kreturn ← withLocalDeclD outerReturnCont.resultName outerReturnCont.resultType fun r => do
        mkLambdaFVars #[r] (← outerReturnCont.k)
      let ksuccess ← withLocalDeclD dec.resultName dec.resultType fun r => do
        mkLambdaFVars #[r] (← dec.k)
      let β ← mkMonadicType (← read).doBlockResultType
      return mkApp6 (mkConst ``EarlyReturn.runK [mi.u, mi.v]) ρ dec.resultType β e kreturn ksuccess
    m.restoreCont { resultName, resultType, k }
where
  mi := m.monadInfo
  stM α := mkApp2 (mkConst ``Except [mi.u, mi.u]) ρ α

structure BreakControlStack extends ControlStack where
  synthesizeBreak : ContVarId → DoElabM Unit
  synthesizeContinue : ContVarId → DoElabM Unit

def ControlStack.breakT (m : ControlStack) : BreakControlStack where
  monadInfo :=
    { mi with m := mkApp (mkConst ``BreakT [mi.u, mi.v]) mi.m }
  instMonad :=
    mkApp3 (mkConst ``ExceptT.instMonad [mi.u, mi.v]) bc mi.m m.instMonad
  stM := m.stM ∘ stM
  runInBase e := do
    -- `e : BreakT m α`. Return `e`, which is defeq to `ExceptT.run e`.
    -- See also `instMonadControlExceptTOfMonad.liftWith`.
    return e
  restoreCont dec := do
    -- Wrap `dec` such that the result type is `Except BreakContinue dec.resultType` by unpacking
    -- the exception, calling `dec.k` in the success case.
    -- See also `instMonadControlExceptTOfMonad.restoreM`.
    let resultName ← mkFreshUserName `e
    let resultType := stM dec.resultType
    let k := do
      let e ← getFVarFromUserName resultName
      let some outerBreakCont ← getBreakCont
        | throwError "`break` must be nested inside a loop"
      let some outerContinueCont ← getContinueCont
        | throwError "`continue` must be nested inside a loop"
      let kbreak ← withLocalDeclD (← mkFreshUserName `r) (mkConst ``Unit) fun r => do
        mkLambdaFVars #[r] (← outerBreakCont)
      let kcontinue ← withLocalDeclD (← mkFreshUserName `r) (mkConst ``Unit) fun r => do
        mkLambdaFVars #[r] (← outerContinueCont)
      let ksuccess ← withLocalDeclD dec.resultName dec.resultType fun r => do
        mkLambdaFVars #[r] (← dec.k)
      let β ← mkMonadicType (← read).doBlockResultType
      return mkApp6 (mkConst ``Break.runK [mi.u, mi.v]) dec.resultType β e kbreak kcontinue ksuccess
    m.restoreCont { resultName, resultType, k }
  synthesizeBreak kvar := do
    kvar.synthesizeJumps do
      m.runInBase <| mkApp2 (mkConst ``BreakT.break [mi.u, mi.v]) mi.m m.instMonad
  synthesizeContinue kvar := do
    kvar.synthesizeJumps do
      m.runInBase <| mkApp2 (mkConst ``BreakT.continue [mi.u, mi.v]) mi.m m.instMonad
where
  mi := m.monadInfo
  bc := mkConst ``BreakContinue [mi.u]
  stM α := mkApp2 (mkConst ``Except [mi.u, mi.u]) bc α

def ControlStack.synthesizePure (m : ControlStack) (resultName : Name) (pureKVar : ContVarId) : DoElabM Unit := do
  pureKVar.synthesizeJumps do
    let r ← getFVarFromUserName resultName
    let mi := m.monadInfo
    let instMonad := m.instMonad
    let instPure := instMonad |> mkApp2 (mkConst ``Monad.toApplicative [mi.u, mi.v]) mi.m
                              |> mkApp2 (mkConst ``Applicative.toPure [mi.u, mi.v]) mi.m
    m.runInBase <| mkApp4 (mkConst ``Pure.pure [mi.u, mi.v])
      mi.m instPure (← inferType r) r

structure ControlLifter where
  mutVars : Array Name
  monadInfo : MonadInfo
  instMonad : Expr
  successCont : DoElemCont
  pureKVar : ContVarId
  breakKVar : ContVarId
  continueKVar : ContVarId
  returnCont : DoElemCont
  hasEarlyReturn : MetaM Bool
  resultType : Expr

meta def ControlLifter.ofCont (dec : DoElemCont) : DoElabM ControlLifter := do
  let mi := (← read).monadInfo
  let oldReturnCont ← getReturnCont
  -- γ is the result type of the `try` block. It is `stM m (t m)` for whatever `t` is necessary
  -- to restore reassigned mut vars, early `return`, `break` and `continue`.
  let γ ← mkFreshResultType `γ
  let mutVars := (← read).mutVars
  let pureKVar ← mkFreshContVar γ (mutVars.push dec.resultName)
  let returnMVar ← mkFreshExprMVar (mkConst ``Unit)
  let breakKVar ← mkFreshContVar γ mutVars
  let continueKVar ← mkFreshContVar γ mutVars
  let ρ := oldReturnCont.resultType
  let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
  -- We can fill in `returnK` immediately because it does not influence reassigned mut vars
  let returnCont := { oldReturnCont with k := do
    -- The following line is purely so that we know whether there was an early return at all
    discard <| isDefEq returnMVar (mkConst ``Unit.unit)
    let r ← getFVarFromUserName oldReturnCont.resultName
    -- TODO: Can we construct γ later on? It must be stM of the transformer stack above
    -- `EarlyReturnT`.
    return mkApp5 (mkConst ``EarlyReturnT.return [mi.u, mi.v]) ρ mi.m (← mkFreshResultType `δ) instMonad r }
  let hasEarlyReturn := returnMVar.mvarId!.isAssigned
  return { mutVars, monadInfo := mi, instMonad, successCont := dec, pureKVar, breakKVar, continueKVar, returnCont, hasEarlyReturn, resultType := γ }

meta def ControlLifter.lift (l : ControlLifter) (elabElem : DoElemElab) : DoElabM Expr := do
  let oldBreakCont ← getBreakCont
  let oldContinueCont ← getContinueCont
  let breakCont := Functor.mapConst l.breakKVar.mkJump oldBreakCont
  let continueCont := Functor.mapConst l.continueKVar.mkJump oldContinueCont
  let returnCont := l.returnCont
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  let pureCont := { l.successCont with k := l.pureKVar.mkJump }
  withReader (fun ctx => { ctx with contInfo, doBlockResultType := l.resultType }) <| elabElem pureCont

meta def ControlLifter.synthesizeConts (l : ControlLifter) (breakT? : Option Bool := none) (stateT? : Option Bool := none) (earlyReturnT? : Option Bool := none) : DoElabM (ControlStack × Array Name) := do
  let reassignedMutVars ← do
    let rootCtx := (← l.resultType.mvarId!.getDecl).lctx
    let pur ← l.pureKVar.getReassignedMutVars rootCtx
    let brk ← l.breakKVar.getReassignedMutVars rootCtx
    let cnt ← l.continueKVar.getReassignedMutVars rootCtx
    pure <| l.mutVars.filter (pur.union brk |>.union cnt).contains
  let breakT := breakT? = some true || (← l.breakKVar.jumpCount) > 0 || (← l.continueKVar.jumpCount) > 0
  let stateT := stateT? = some true || (reassignedMutVars.size > 0)
  let earlyReturnT := earlyReturnT? = some true || (← l.hasEarlyReturn)
  let mut controlStack := ControlStack.base l.monadInfo l.instMonad
  if earlyReturnT then
    controlStack := ControlStack.earlyReturnT l.returnCont.resultType controlStack
  if stateT then
    let tys ← reassignedMutVars.mapM fun v => return (← getLocalDeclFromUserName v).type
    let σ ← mkProdN tys
    controlStack := ControlStack.stateT reassignedMutVars σ controlStack
  if breakT then
    let breakStack := ControlStack.breakT controlStack
    breakStack.synthesizeBreak l.breakKVar
    breakStack.synthesizeContinue l.continueKVar
    controlStack := breakStack.toControlStack
  synthUsingDefEq "result type" l.resultType (controlStack.stM l.successCont.resultType)
  controlStack.synthesizePure l.successCont.resultName l.pureKVar
  return (controlStack, reassignedMutVars)

meta def ControlLifter.restoreCont (l : ControlLifter) : DoElabM DoElemCont := do
  let (controlStack, _reassignedMutVars) ← l.synthesizeConts
  controlStack.restoreCont l.successCont

/--
Introduce proxy redefinitions for *all* mut vars and call the continuation `k` with a function
`elimProxyDefs : Expr → MetaM Expr` similar to `mkLetFVars` that will replace the proxy defs with
the actual reassigned or original definitions.
-/
@[inline]
meta def withProxyMutVarDefs [Inhabited α] (k : (Expr → MetaM Expr) → DoElabM α) : DoElabM α := do
  let mutVars := (← read).mutVars
  let outerCtx ← getLCtx
  let outerDecls := mutVars.map outerCtx.getFromUserName!
  -- for decl in outerDecls do
  --   outerCtx := outerCtx.addDecl (decl.setNondep true)
  -- withLCtx' outerCtx do
  withLocalDeclsDND (← outerDecls.mapM fun x => do return (x.userName, x.type)) (kind := .implDetail) fun proxyDefs => do
    let proxyCtx ← getLCtx
    let elimProxyDefs e : MetaM Expr := do
      let innerCtx ← getLCtx

      let actualDefs := proxyDefs.map fun pDef =>
        let x := (proxyCtx.getFVar! pDef).userName
        let iDef := (innerCtx.getFromUserName! x).toExpr
        if iDef == pDef then
          (outerCtx.getFromUserName! x).toExpr  -- original definition
        else
          iDef                                  -- reassigned definition
      let e ← elimMVarDeps proxyDefs e
      return e.replaceFVars proxyDefs actualDefs
    k elimProxyDefs

mutual
  meta def elabElem (dooElem : TSyntax `dooElem) (dec : DoElemCont) : DoElabM Expr := withRef dooElem do
    match dooElem with
    -- First off the three constructs that discard the continuation `k`:
    | `(dooElem| return $e) =>
      let returnCont ← getReturnCont
      let e ← Term.elabTermEnsuringType e returnCont.resultType
      mapLetDeclZeta returnCont.resultName returnCont.resultType e fun _ =>
        returnCont.k
    | `(dooElem| break) =>
      let some breakCont := (← getBreakCont)
        | throwError "`break` must be nested inside a loop"
      breakCont
      -- NB: discard continuation `k?`, unconditionally
    | `(dooElem| continue) =>
      let some continueCont := (← getContinueCont)
        | throwError "`continue` must be nested inside a loop"
      continueCont
    | `(dooElem| $e:term) =>
      let mα ← mkMonadicType dec.resultType
      let e ← Term.elabTermEnsuringType e mα
      dec.mkBindUnlessPure e
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? ← $rhs) =>
      checkMutVarsForShadowing x.getId
      let xType ← elabType xType?
      let lctx ← getLCtx
      let mutVars := (← read).mutVars
      elabElem rhs <| .mk x.getId xType do
        withLCtxKeepingMutVarDefs lctx mutVars x.getId do
          declareMutVar? mutTk? x.getId dec.continueWithUnit
    | `(dooElem| $x:ident ← $rhs) =>
      throwUnlessMutVarDeclared x.getId
      let xType := (← getLocalDeclFromUserName x.getId).type
      let lctx ← getLCtx
      let mutVars := (← read).mutVars
      elabElem rhs <| .mk x.getId xType do
        withLCtxKeepingMutVarDefs lctx mutVars x.getId do
          dec.continueWithUnit
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? := $rhs) =>
      checkMutVarsForShadowing x.getId
      -- We want to allow `do let foo : Nat = Nat := rfl; pure (foo ▸ 23)`. Note that the type of
      -- foo has sort `Sort 0`, whereas the sort of the monadic result type `Nat` is `Sort 1`.
      -- Hence `freshLevel := true` (yes, even for `mut` vars; why not?).
      let xType ← elabType xType? (freshLevel := true)
      let rhs ← Term.elabTermEnsuringType rhs xType
      mapLetDecl (usedLetOnly := false) x.getId xType rhs fun _xdefn => declareMutVar? mutTk? x.getId dec.continueWithUnit
    | `(dooElem| $x:ident := $rhs) =>
      throwUnlessMutVarDeclared x.getId
      let xType := (← getLocalDeclFromUserName x.getId).type
      let rhs ← Term.elabTermEnsuringType rhs xType
      mapLetDecl (usedLetOnly := false) x.getId xType rhs fun _xdefn => dec.continueWithUnit
    | `(dooElem| if $cond then $thenDooSeq $[else $elseDooSeq?]?) =>
      dec.withDuplicableCont fun dec => do
        let then_ ← elabElems1 (getDooElems thenDooSeq) dec
        let else_ ← match elseDooSeq? with
          | none => dec.continueWithUnit
          | some elseDooSeq => elabElems1 (getDooElems elseDooSeq) dec
        let then_ ← Term.exprToSyntax then_
        let else_ ← Term.exprToSyntax else_
        Term.elabTerm (← `(if $cond then $then_ else $else_)) none
    | `(dooElem| doo $dooSeq) => elabElems1 (getDooElems dooSeq) dec
    | `(dooElem| for $x:ident in $xs doo $dooSeq) =>
      -- set_option pp.universes true in #print forBreakMem_
      let uα ← mkFreshLevelMVar
      let uρ ← mkFreshLevelMVar
      let α ← mkFreshExprMVar (mkSort (mkLevelSucc uα)) (userName := `α)
      let ρ ← mkFreshExprMVar (mkSort (mkLevelSucc uρ)) (userName := `ρ)
      let xs ← Term.elabTermEnsuringType xs ρ
      let mi := (← read).monadInfo
      let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
      let σ ← mkFreshExprMVar (mkSort (mkLevelSucc mi.u)) (userName := `σ)
      let returnCont ← getReturnCont
      let ε := returnCont.resultType
      let γ := (← read).doBlockResultType
      let β ← mkArrow σ (← mkMonadicType γ)
      let mutVars := (← read).mutVars
      let breakRhs ← mkFreshExprMVar β
      withLetDecl (← mkFreshUserName `kbreak) β breakRhs (kind := .implDetail) (nondep := true) fun kbreak => do
      withLocalDeclD x.getId α fun x => do
      withLocalDecl (← mkFreshUserName `kcontinue) .default β (kind := .implDetail) fun kcontinue => do
      withLocalDecl (← mkFreshUserName `s) .default σ (kind := .implDetail) fun loopS => do
      withProxyMutVarDefs fun elimProxyDefs => do
        let rootCtx ← getLCtx
        let continueKVar ← mkFreshContVar γ mutVars
        let breakKVar ← mkFreshContVar γ mutVars

        -- Elaborate the loop body, which must have result type `PUnit`.
        let body ← enterLoopBody γ (← getReturnCont) breakKVar.mkJump continueKVar.mkJump do
          elabElems1 (getDooElems dooSeq) { dec with k := continueKVar.mkJump }

        -- Compute the set of mut vars that were reassigned on the path to a back jump (`continue`).
        -- Take care to preserve the declaration order that is manifest in the array `mutVars`.
        let loopMutVars ← do
          let ctn ← continueKVar.getReassignedMutVars rootCtx
          let brk ← breakKVar.getReassignedMutVars rootCtx
          pure (ctn.union brk)
        let loopMutVars := mutVars.filter loopMutVars.contains

        -- Assign the state tuple type and the initial tuple of states.
        let preS ← σ.mvarId!.withContext do
          let defs ← loopMutVars.mapM (getFVarFromUserName ·)
          let (tuple, tupleTy) ← mkProdMkN defs
          synthUsingDefEq "state tuple type" σ tupleTy
          pure tuple

        -- Synthesize the `continue` and `break` jumps.
        continueKVar.synthesizeJumps do
          let (tuple, _tupleTy) ← mkProdMkN (← loopMutVars.mapM (getFVarFromUserName ·))
          return mkApp kcontinue tuple
        breakKVar.synthesizeJumps do
          let (tuple, _tupleTy) ← mkProdMkN (← loopMutVars.mapM (getFVarFromUserName ·))
          return mkApp kbreak tuple

        -- Elaborate the continuation, now that `σ` is known. It will be the `break` handler.
        -- If there is a `break`, the code will be shared in the `kbread` join point.
        breakRhs.mvarId!.withContext do
          let e ← withLocalDeclD (← mkFreshUserName `s) σ fun postS => do mkLambdaFVars #[postS] <| ← do
            bindMutVarsFromTuple loopMutVars.toList postS.fvarId! do
              dec.continueWithUnit
          synthUsingDefEq "break RHS" breakRhs e

        -- Finally eliminate the proxy variables from the loop body.
        -- * Point non-reassigned mut var defs to the pre state
        -- * Point the initial defs of reassigned mut vars to the loop state
        -- Done by `elimProxyDefs` below.
        let body ← bindMutVarsFromTuple loopMutVars.toList loopS.fvarId! do
          elimProxyDefs body

        let hadBreak := (← breakKVar.jumpCount) > 0
        let kcons ← mkLambdaFVars #[x, kcontinue, loopS] body
        let knil := if hadBreak then kbreak else breakRhs
        let instFoldable ← Term.mkInstMVar <| mkApp2 (mkConst ``Foldable [uρ, uα, mi.u, mi.v]) ρ α
        let app := mkConst ``Foldable.foldrEta [uρ, uα, mi.u, mi.v]
        let app := mkApp9 app ρ α instFoldable σ (← mkMonadicType γ) kcons knil xs preS
        if hadBreak then
          mkLetFVars (generalizeNondepLet := false) #[kbreak] app
        else
          return (← elimMVarDeps #[kbreak] app).replaceFVar kbreak breakRhs

    | `(dooElem| for $x:ident in $xs invariant $cursorBinder $stateBinders* => $body doo $dooSeq) =>
      --trace[Elab.do] "cursorBinder: {cursorBinder}"
      let call ← elabElem (← `(dooElem| for $x:ident in $xs doo $dooSeq)) dec
      let_expr Foldable.foldrEta ρ α instFoldable σ mγ kcons knil xs s := call
        | throwError "Internal elaboration error: `for` loop did not elaborate to a call of `Foldable.foldr`."
      let γ ← mkFreshResultType `γ
      synthUsingDefEq "continuation type" mγ (← mkMonadicType γ)
      call.withApp fun head args => do
      let [u, v, w, x] := head.constLevels!
        | throwError "`Foldable.foldrEta` had wrong number of levels {head.constLevels!}"
      let mi := (← read).monadInfo
      unless ← isLevelDefEq mi.u (mkLevelMax v w) do
        throwError "The universe level of the monadic result type {mi.u} was not the maximum of that of the state tuple {w} and elements {v}. Cannot elaborate invariants for this case."
      unless ← isLevelDefEq mi.v x do
        throwError "The universe level of the result type {mi.v} and that of the continuation result type {x} were different. Cannot elaborate invariants for this case."
      -- First the non-ghost arguments
      let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
      let app := mkConst ``Foldable.foldrEtaInv [u, v, w, x]
      let app := mkApp7 app ρ α instFoldable mi.m instMonad σ γ
      let app := mkApp4 app kcons knil xs s
      -- Now the ghost arguments
      let instFoldable ← Term.mkInstMVar (mkApp2 (mkConst ``Foldable [u, v, v, v]) ρ α)
      let ps ← mkFreshExprMVar (mkConst ``Std.Do.PostShape [mi.u])
      let instWP ← Term.mkInstMVar (mkApp2 (mkConst ``Std.Do.WP [mi.u, mi.v]) (← read).monadInfo.m ps)
      let xsToList := mkApp4 (mkConst ``Foldable.toList [u, v, v]) ρ α instFoldable xs
      let inv ← mkFreshExprMVar (mkApp4 (mkConst ``Std.Do.Invariant [v, mi.u]) α xsToList σ ps)
      let cursor := mkApp2 (mkConst ``List.Cursor [v]) α xsToList
      let assertion := mkApp (mkConst ``Std.Do.Assertion [mi.u]) ps
      let mutVarsTuple ← Term.exprToSyntax s
      let cursorσ := mkApp2 (mkConst ``Prod [v, mi.u]) cursor σ
      let syn ← `(fun ($cursorBinder, $mutVarsTuple) $stateBinders* => $body)
      let success ← Term.elabFun (← `(fun ($cursorBinder, $mutVarsTuple) $stateBinders* => $body)) (← mkArrow cursorσ assertion)
      let inv := mkApp3 (mkConst ``Std.Do.PostCond.noThrow [mkLevelMax v mi.u]) ps cursorσ success
      return mkApp4 app instFoldable ps instWP inv
-- Why doesn't the following work?
--    | `(dooElem| try $trySeq:dooSeq $[$catchSeqs:dooCatch]* $[finally $finSeq?]?) =>
    | `(dooElem| try $trySeq:dooSeq $[catch $xs $[: $eTypes?]? => $catchSeqs]* $[finally $finSeq?]?) =>
      for x in xs do if x.raw.isIdent then
        checkMutVarsForShadowing x.raw.getId
      if catchSeqs.isEmpty && finSeq?.isNone then
        throwError "Invalid `try`. There must be a `catch` or `finally`."
      -- We cannot use join points because `tryCatch` and `tryFinally` are never tail-resumptive.
      -- (Proof: `do tryCatch e h; throw x ≠ tryCatch (do e; throw x) (fun e => do h e; throw x)`)
      -- This is also known as the "algebraicity property" in the algebraic effects and handlers
      -- community.
      --
      -- So we need to pack up our effects and unpack them after the `try`.
      -- We could optimize for the `.last` case by omitting the state tuple ... in the future.
      let mi := (← read).monadInfo
      let lifter ← ControlLifter.ofCont dec
      let body ← lifter.lift (elabElems1 (getDooElems trySeq))
      let body ← xs.zip (eTypes?.zip catchSeqs) |>.foldlM (init := body) fun body (x, eType?, catchSeq) => do
        let x := Term.mkExplicitBinder x.raw[0] <| match eType? with
          | some eType => eType
          | none => mkHole x
        let (catch_, ε, uε) ← elabBinder x fun x => do
          let ε ← inferType x
          let uε ← getDecLevel ε
          let catch_ ← lifter.lift (elabElems1 (getDooElems catchSeq))
          let catch_ ← mkLambdaFVars #[x] catch_
          return (catch_, ε, uε)
        if eType?.isSome then
          let inst ← Term.mkInstMVar <| mkApp2 (mkConst ``MonadExceptOf [uε, mi.u, mi.v]) ε mi.m
          return mkApp6 (mkConst ``tryCatchThe [uε, mi.u, mi.v])
            ε mi.m inst lifter.resultType body catch_
        else
          let inst ← Term.mkInstMVar <| mkApp2 (mkConst ``MonadExcept [uε, mi.u, mi.v]) ε mi.m
          return mkApp6 (mkConst ``MonadExcept.tryCatch [uε, mi.u, mi.v])
            ε mi.m inst lifter.resultType body catch_
      let body ← match finSeq? with
        | none => pure body
        | some finSeq => do
          let β ← mkFreshResultType `β
          let fin ← enterFinally β <| elabElems1 (getDooElems finSeq) (← DoElemCont.mkPure β)
          let instMonadFinally ← Term.mkInstMVar <| mkApp (mkConst ``MonadFinally [mi.u, mi.v]) mi.m
          let instFunctor ← Term.mkInstMVar <| mkApp (mkConst ``Functor [mi.u, mi.v]) mi.m
          pure <| mkApp7 (mkConst ``tryFinally [mi.u, mi.v])
            mi.m lifter.resultType β instMonadFinally instFunctor body fin
      (← lifter.restoreCont).mkBindUnlessPure body
    | _ => throwError "unexpected do element {dooElem}, {repr dooElem}"

  meta def elabElems1 (dooElems : Array (TSyntax `dooElem)) (k : DoElemCont) : DoElabM Expr := do
    let last := dooElems.back!
    let init := dooElems.pop
    let unit ← mkPUnit
    let r ← mkFreshUserName `r
    init.foldr (init := elabElem last k) fun el k => elabElem el (.mk r unit k)

end

meta def elabDooBlock (dooSeq : TSyntax `dooSeq) (expectedType? : Expr) : TermElabM Expr := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let cont ← DoElemCont.mkPure ctx.doBlockResultType
  let res ← elabElems1 (getDooElems dooSeq) cont |>.run ctx |>.run' {}
  -- logInfo m!"res: {res}"
  trace[Elab.do] "{res}"
  pure res

elab_rules : term <= expectedType?
  | `(dooBlock| doo $dooSeq) => elabDooBlock dooSeq expectedType?

set_option trace.Elab.do true in
set_option pp.raw false in
#check Id.run (α := Nat) doo
  let mut x ← pure 42
  let y ←
    if true then
      pure 42
    else
      pure 31
  x := x + y
  return x
set_option pp.mvars.delayed false in
set_option trace.Meta.synthInstance true in
set_option trace.Elab.step false in
set_option trace.Elab.do true in
set_option trace.Elab.postpone true in
set_option pp.raw false in
#check doo return 42
#check doo pure (); return 42
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
#check doo let mut x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check doo let x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
set_option trace.Elab.do true in
#check Id.run doo ExceptT.run doo
  let e ← try
      let x := 0
      throw "error"
    catch e : String =>
      pure e
  return e

set_option trace.compiler.ir.result true in
example (x : DoResultPRBC α PEmpty σ) : Nat :=
  match x with
  | .pure _ _ => 0
  | .break _ => 1
  | .continue _ => 2

set_option trace.Compiler.saveBase true in
example (x : Option PEmpty) : Nat :=
  match x with
  | none => 0

set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  for i in [1,2,3] doo
    x := x + i
  return x

set_option trace.Compiler.saveBase true in
set_option trace.Compiler.specialize.step true in
set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  for i in [1,2,3] doo
    for j in [i:10].toList doo
      x := x + i + j
  return x

set_option trace.Elab.do true in
set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.assign true in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    for j in [4,5,6] doo
      if j < 5 then z := z + j
      if j < 3 then continue
      if j > 6 then break
  return z

set_option trace.Compiler.saveBase true in
set_option trace.Elab.do true in
#eval Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    for j in [i:10].toList doo
      if j < 5 then z := z + j
      z := z + i
  return x + y + z

/--
info: (let x := 42;
  let y := 0;
  let z := 1;
  Foldable.foldrEta
    (fun i kcontinue s =>
      let x := s.fst;
      let z := s.snd;
      let x_1 := x + i;
      have __do_jp := fun z r =>
        let z := z + i;
        kcontinue (x_1, z);
      if x_1 > 10 then
        let z := z + i;
        __do_jp z PUnit.unit
      else __do_jp z PUnit.unit)
    (fun s =>
      let x := s.fst;
      let z := s.snd;
      pure (x + y + z))
    [1, 2, 3] (x, z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    if x > 10 then z := z + i
    z := z + i
  return x + y + z)

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.isDefEq.delta true in
-- set_option trace.Meta.isDefEq.assign true in
-- set_option trace.Elab.do true in
/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  have kbreak := fun s =>
    let x := s.fst;
    let s := s.snd;
    let y := s.fst;
    let z := s.snd;
    pure (w + x + y + z);
  Foldable.foldrEta
    (fun i kcontinue s =>
      let x := s.fst;
      let s := s.snd;
      let y := s.fst;
      let z := s.snd;
      if x < 20 then
        let y := y - 2;
        kbreak (x, y, z)
      else
        have __do_jp := fun z r =>
          if x > 10 then
            let x := x + 3;
            kcontinue (x, y, z)
          else
            let x := x + i;
            kcontinue (x, y, z);
        if x = 3 then
          let z := z + i;
          __do_jp z PUnit.unit
        else __do_jp z PUnit.unit)
    kbreak [1, 2, 3] (x, y, z)).run : Nat
-/
#guard_msgs (info) in
#check Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 49
    def List.foldrEta._at_.Do._example.spec_0 w x.1 x.2 : Nat :=
      fun kbreak.3 s.4 : Nat :=
        let x := s.4 # 0;
        let s.5 := s.4 # 1;
        let y := s.5 # 0;
        let z := s.5 # 1;
        let _x.6 := Nat.add w x;
        let _x.7 := Nat.add _x.6 y;
        let _x.8 := Nat.add _x.7 z;
        return _x.8;
      fun _f.9 i kcontinue.10 s.11 : Nat :=
        let x := s.11 # 0;
        let s.12 := s.11 # 1;
        let y := s.12 # 0;
        jp _jp.13 z : Nat :=
          let _x.14 := 10;
          let _x.15 := Nat.decLt _x.14 x;
          cases _x.15 : Nat
          | Decidable.isFalse x.16 =>
            let x := Nat.add x i;
            let _x.17 := @Prod.mk _ _ y z;
            let _x.18 := @Prod.mk _ _ x _x.17;
            let _x.19 := kcontinue.10 _x.18;
            return _x.19
          | Decidable.isTrue x.20 =>
            let _x.21 := 3;
            let x := Nat.add x _x.21;
            let _x.22 := @Prod.mk _ _ y z;
            let _x.23 := @Prod.mk _ _ x _x.22;
            let _x.24 := kcontinue.10 _x.23;
            return _x.24;
        let z := s.12 # 1;
        let _x.25 := 20;
        let _x.26 := Nat.decLt x _x.25;
        cases _x.26 : Nat
        | Decidable.isFalse x.27 =>
          let _x.28 := 3;
          let _x.29 := instDecidableEqNat x _x.28;
          cases _x.29 : Nat
          | Decidable.isFalse x.30 =>
            goto _jp.13 z
          | Decidable.isTrue x.31 =>
            let z := Nat.add z i;
            goto _jp.13 z
        | Decidable.isTrue x.32 =>
          let _x.33 := 2;
          let y := Nat.sub y _x.33;
          let _x.34 := @Prod.mk _ _ y z;
          let _x.35 := @Prod.mk _ _ x _x.34;
          let _x.36 := kbreak.3 _x.35;
          return _x.36;
      cases x.1 : Nat
      | List.nil =>
        let _x.37 := kbreak.3 x.2;
        return _x.37
      | List.cons head.38 tail.39 =>
        let _x.40 := @List.foldrEta _ _ _ _f.9 kbreak.3 tail.39;
        let _x.41 := _f.9 head.38 _x.40 x.2;
        return _x.41
[Compiler.saveBase] size: 13
    def Do._example : Nat :=
      let w := 23;
      let x := 42;
      let y := 0;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ y z;
      let _x.8 := @Prod.mk _ _ x _x.7;
      let _x.9 := List.foldrEta._at_.Do._example.spec_0 w _x.6 _x.8;
      return _x.9
-/
#guard_msgs in
example := Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z

set_option trace.Elab.do true in
/--
trace: [Elab.do] let x := 42;
    let y := 0;
    have kbreak := fun s =>
      let x := s;
      pure (x + x + x + x);
    Foldable.foldrEta
      (fun i kcontinue s =>
        let x := s;
        have __do_jp := fun x_1 r =>
          if x_1 > 10 then
            let x := x_1 + 3;
            kcontinue x
          else
            if x_1 < 20 then
              let x := x_1 - 2;
              kbreak x
            else
              let x := x_1 + i;
              kcontinue x;
        if x = 3 then
          let x := x + 1;
          __do_jp x PUnit.unit
        else __do_jp x PUnit.unit)
      kbreak [1, 2, 3] x
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  for i in [1,2,3] doo
    if x = 3 then x := x + 1
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x - 2; break
    x := x + i
  return x + x + x + x

/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  do
  let r ←
    forIn [1, 2, 3] ⟨x, y, z⟩ fun i r =>
        let x := r.fst;
        let x_1 := r.snd;
        let y := x_1.fst;
        let z := x_1.snd;
        let __do_jp := fun x y z y_1 =>
          let __do_jp := fun x z y_2 =>
            let __do_jp := fun x y_3 =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨x, y, z⟩);
            if x > 10 then
              let x := x + 3;
              pure (ForInStep.yield ⟨x, y, z⟩)
            else do
              let y ← pure PUnit.unit
              __do_jp x y;
          if x = 3 then
            let z := z + i;
            do
            let y ← pure PUnit.unit
            __do_jp x z y
          else do
            let y ← pure PUnit.unit
            __do_jp x z y;
        if x < 20 then
          let y := y - 2;
          pure (ForInStep.done ⟨x, y, z⟩)
        else do
          let y_1 ← pure PUnit.unit
          __do_jp x y z y_1
  match r with
    | ⟨x, y, z⟩ => pure (w + x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x < 20 then y := y - 2; break
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    x := x + i
  return w + x + y + z)

set_option trace.Elab.do true in
set_option trace.Compiler.saveBase true in
/--
trace: [Elab.do] let x := 42;
    have kbreak := fun s =>
      let x := s;
      let x := x + 13;
      let x := x + 13;
      let x := x + 13;
      let x := x + 13;
      pure x;
    Foldable.foldrEta
      (fun i kcontinue s =>
        let x := s;
        if x = 3 then pure x
        else
          if x > 10 then
            let x := x + 3;
            kcontinue x
          else
            if x < 20 then
              let x := x * 2;
              kbreak x
            else
              let x := x + i;
              kcontinue x)
      kbreak [1, 2, 3] x
---
trace: [Compiler.saveBase] size: 31
    def List.foldrEta._at_.Do._example.spec_0 x.1 x.2 : Nat :=
      fun kbreak.3 s.4 : Nat :=
        let _x.5 := 13;
        let x := Nat.add s.4 _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        return x;
      cases x.1 : Nat
      | List.nil =>
        let _x.6 := kbreak.3 x.2;
        return _x.6
      | List.cons head.7 tail.8 =>
        let _x.9 := 3;
        let _x.10 := instDecidableEqNat x.2 _x.9;
        cases _x.10 : Nat
        | Decidable.isFalse x.11 =>
          let _x.12 := 10;
          let _x.13 := Nat.decLt _x.12 x.2;
          cases _x.13 : Nat
          | Decidable.isFalse x.14 =>
            let _x.15 := 20;
            let _x.16 := Nat.decLt x.2 _x.15;
            cases _x.16 : Nat
            | Decidable.isFalse x.17 =>
              let x := Nat.add x.2 head.7;
              let _x.18 := List.foldrEta._at_.Do._example.spec_0 tail.8 x;
              return _x.18
            | Decidable.isTrue x.19 =>
              let _x.20 := 2;
              let x := Nat.mul x.2 _x.20;
              let _x.21 := kbreak.3 x;
              return _x.21
          | Decidable.isTrue x.22 =>
            let x := Nat.add x.2 _x.9;
            let _x.23 := List.foldrEta._at_.Do._example.spec_0 tail.8 x;
            return _x.23
        | Decidable.isTrue x.24 =>
          return x.2
[Compiler.saveBase] size: 9
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.foldrEta._at_.Do._example.spec_0 _x.7 x;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] doo
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 31
    def List.foldrEta._at_.Do._example.spec_0 x.1 x.2 : Nat :=
      fun kbreak.3 s.4 : Nat :=
        let _x.5 := 13;
        let x := Nat.add s.4 _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        let x := Nat.add x _x.5;
        return x;
      cases x.1 : Nat
      | List.nil =>
        let _x.6 := kbreak.3 x.2;
        return _x.6
      | List.cons head.7 tail.8 =>
        let _x.9 := 3;
        let _x.10 := instDecidableEqNat x.2 _x.9;
        cases _x.10 : Nat
        | Decidable.isFalse x.11 =>
          let _x.12 := 10;
          let _x.13 := Nat.decLt _x.12 x.2;
          cases _x.13 : Nat
          | Decidable.isFalse x.14 =>
            let _x.15 := 20;
            let _x.16 := Nat.decLt x.2 _x.15;
            cases _x.16 : Nat
            | Decidable.isFalse x.17 =>
              let x := Nat.add x.2 head.7;
              let _x.18 := List.foldrEta._at_.Do._example.spec_0 tail.8 x;
              return _x.18
            | Decidable.isTrue x.19 =>
              let _x.20 := 2;
              let x := Nat.mul x.2 _x.20;
              let _x.21 := kbreak.3 x;
              return _x.21
          | Decidable.isTrue x.22 =>
            let x := Nat.add x.2 _x.9;
            let _x.23 := List.foldrEta._at_.Do._example.spec_0 tail.8 x;
            return _x.23
        | Decidable.isTrue x.24 =>
          return x.2
[Compiler.saveBase] size: 9
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.foldrEta._at_.Do._example.spec_0 _x.7 x;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] doo
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Elab.do true in
set_option trace.Compiler.saveBase true in
/--
trace: [Elab.do] let x := 42;
    let y := 0;
    let z := 1;
    Foldable.foldrEta
      (fun i kcontinue s =>
        let x := s.fst;
        let z := s.snd;
        let x_1 := x + i;
        Foldable.foldrEta
          (fun j kcontinue_1 s_1 =>
            let z_1 := s_1;
            let z := z_1 + x_1 + j;
            kcontinue_1 z)
          (fun s =>
            let z := s;
            kcontinue (x_1, z))
          [i:10].toList z)
      (fun s =>
        let x := s.fst;
        let z := s.snd;
        pure (x + y + z))
      [1, 2, 3] (x, z)
---
trace: [Compiler.saveBase] size: 24
    def List.foldrEta._at_.Do._example.spec_0 z x.1 x.2 : Nat :=
      cases x.1 : Nat
      | List.nil =>
        let x := x.2 # 0;
        let z := x.2 # 1;
        let _x.3 := Nat.add x z;
        return _x.3
      | List.cons head.4 tail.5 =>
        let x := x.2 # 0;
        let z := x.2 # 1;
        let x := Nat.add x head.4;
        fun _f.6 s.7 : Nat :=
          let _x.8 := @Prod.mk _ _ x s.7;
          let _x.9 := List.foldrEta._at_.Do._example.spec_0 z tail.5 _x.8;
          return _x.9;
        fun _f.10 j kcontinue.11 s.12 : Nat :=
          let _x.13 := Nat.add s.12 x;
          let z := Nat.add _x.13 j;
          let _x.14 := kcontinue.11 z;
          return _x.14;
        let _x.15 := 10;
        let _x.16 := Nat.sub _x.15 head.4;
        let _x.17 := Nat.add _x.16 z;
        let _x.18 := 1;
        let _x.19 := Nat.sub _x.17 _x.18;
        let _x.20 := Nat.mul z _x.19;
        let _x.21 := Nat.add head.4 _x.20;
        let _x.22 := @List.nil _;
        let _x.23 := List.range'TR.go z _x.19 _x.21 _x.22;
        let _x.24 := @List.foldrEta _ _ _ _f.10 _f.6 _x.23 z;
        return _x.24
[Compiler.saveBase] size: 10
    def Do._example : Nat :=
      let x := 42;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ x z;
      let _x.8 := List.foldrEta._at_.Do._example.spec_0 z _x.6 _x.7;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    for j in [i:10].toList doo
      z := z + x + j
  return x + y + z

/--
info: (let x := 42;
  do
  let r ←
    forIn [1, 2, 3] ⟨none, x⟩ fun i r =>
        let r_1 := r.snd;
        let x := r_1;
        let __do_jp := fun x y =>
          let __do_jp := fun x y =>
            let __do_jp := fun x y =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨none, x⟩);
            if x < 20 then
              let x := x * 2;
              pure (ForInStep.done ⟨none, x⟩)
            else do
              let y ← pure PUnit.unit
              __do_jp x y;
          if x > 10 then
            let x := x + 3;
            pure (ForInStep.yield ⟨none, x⟩)
          else do
            let y ← pure PUnit.unit
            __do_jp x y;
        if x = 3 then pure (ForInStep.done ⟨some x, x⟩)
        else do
          let y ← pure PUnit.unit
          __do_jp x y
  let x : Nat := r.snd
  let __do_jp : Nat → PUnit → Id Nat := fun x y =>
    let x := x + 13;
    let x := x + 13;
    let x := x + 13;
    let x := x + 13;
    pure x
  match r.fst with
    | none => do
      let y ← pure PUnit.unit
      __do_jp x y
    | some a => pure a).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x)

open Std.Do in
set_option trace.Elab.do true in
#check Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3]
    invariant xs => ⌜xs.pos = 3⌝ doo
    x := x + i
    for j in [i:10].toList doo
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

open Std.Do in
#check Id.run <| StateT.run (σ:= Nat) (s:=42) doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3]
    invariant xs s => ⌜xs.pos = s⌝ doo
    x := x + i
    for j in [i:10].toList doo
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

example : (Id.run doo pure 42)
        = (Id.run  do pure 42) := by rfl
example : (Id.run doo return 42)
        = (Id.run  do return 42) := by rfl
example {e : Id PUnit} : (Id.run doo e)
                       = (Id.run  do e) := by rfl
example {e : Id PUnit} : (Id.run doo e; return 42)
                       = (Id.run  do e; return 42) := by rfl
example : (Id.run doo let x := 42; return x + 13)
        = (Id.run  do let x := 42; return x + 13) := by rfl
example : (Id.run doo let x ← pure 42; return x + 13)
        = (Id.run  do let x ← pure 42; return x + 13) := by rfl
example : (Id.run doo let mut x := 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x := 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x ← pure 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x)
        = (Id.run  do let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : Nat := Id.run doo let mut foo : Nat = Nat := rfl; pure (foo ▸ 23)
example {e} : (Id.run doo let mut x := 0; let y := 3; let z ← doo { let mut y ← e; x := y + 1; pure y }; let y := y + 3; pure (x + y + z))
            = (Id.run  do let mut x := 0; let y := 3; let z ←  do { let mut y ← e; x := y + 1; pure y }; let y := y + 3; pure (x + y + z)) := by rfl
example : (Id.run doo let x := 0; let y ← let x := x + 1; pure x)
        = (Id.run doo let x := 0; pure x) := by rfl

-- Test: Nested if-then-else with multiple mutable variables
example : (Id.run doo
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y)
= (Id.run do
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y) := by rfl

-- Test: Multiple reassignments in sequence
example : (Id.run doo
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x)
= (Id.run do
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x) := by rfl

-- Test: Monadic bind with complex RHS
example : (Id.run doo
  let x ← (do let y := 5; pure (y + 3))
  return x * 2)
= (Id.run do
  let x ← (do let y := 5; pure (y + 3))
  return x * 2) := by rfl

-- Test: Mutable variable reassignment through monadic bind
example : (Id.run doo
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x)
= (Id.run do
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x) := by rfl

-- Test: Multiple mutable variables with different reassignment patterns
example : (Id.run doo
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c))
= (Id.run do
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c)) := by rfl

-- Test: Let binding followed by mutable reassignment
example : (Id.run doo
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y))
= (Id.run do
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y)) := by rfl

-- Test: Early return in else branch
example : (Id.run doo
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x)
= (Id.run do
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x) := by rfl

-- Test: Both branches return
example : (Id.run doo
  let mut x := 0
  if true then
    return 1
  else
    return 2)
= (Id.run do
  let mut x := 0
  if true then
    return 1
  else
    return 2) := by rfl

-- Test: Three-level nested if with mutable variables
example : (Id.run doo
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x)
= (Id.run do
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x) := by rfl

-- Test: Mutable variable used in condition
example : (Id.run doo
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x)
= (Id.run do
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x) := by rfl

-- Test: Multiple monadic binds in sequence
example : (Id.run doo
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c))
= (Id.run do
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c)) := by rfl

-- Test: Mutable bind in if condition position
example : (Id.run doo
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x)
= (Id.run do
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x) := by rfl

-- Test: Empty else branch behavior
example : (Id.run doo
  let mut x := 5
  if false then
    x := 10
  return x)
= (Id.run do
  let mut x := 5
  if false then
    x := 10
  return x) := by rfl

-- Test: Nested doo with if and early return
example : (Id.run doo
  let mut x := 10
  let y ← doo
    if true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y)
= (Id.run do
  let mut x := 10
  let y ← do
    if true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y) := by rfl

-- Test: For loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  for i in [0:100].toList doo
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x)
= (Id.run do
  let mut x := 42
  for i in [0:100].toList do
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x) := by rfl

-- set_option trace.Meta.synthInstance true in
set_option trace.Elab.do true in
-- Test: Nested for loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    for j in [i:10].toList doo
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z)
= (Id.run do
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z) := by rfl

-- Test: Try/catch
example {try_ : Except String Nat} {catch_ : String → Except String Nat} :
  (Id.run <| ExceptT.run (ε:=String) doo
  let x ←
    try try_ -- TODO: investigate why we can't put it on the same line
    catch e => catch_ e
  return x + 23)
= (Id.run <| ExceptT.run (ε:=String) do
  let x ← try try_ catch e => catch_ e
  return x + 23) := by simp

-- Test: Try/catch with throw in continuation (i.e., `tryCatch` is non-algebraic)
example :
  (Id.run <| ExceptT.run (ε:=String) doo
  try pure ()
  catch e => pure ()
  throw (α:=Nat) "error")
= throw (α:=Nat) "error" := by rfl

#check (Id.run <| ExceptT.run (ε:=String) doo
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
      return ()
    else
      x := 5
  catch e =>
    x := x + 1)

#check (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      throw "error"
      return ()
    else
      pure ()
  catch e =>
    pure ())

-- Try/catch with reassignment
example :
  (Id.run <| ExceptT.run (ε:=String) doo
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
    else
      x := 5
  catch e =>
    x := x + 1
  return x)
= (Id.run <| ExceptT.run (ε:=String) do
  let mut x := 0
  try
    if true then
      x := 10
      throw "error"
    else
      x := 5
  catch e =>
    x := x + 1
  return x) := by rfl

#check (Id.run <| StateT.run' (σ := Nat) (s := 42) <| ExceptT.run (ε:=String) doo
  try
    pure ()
  finally
    set 0
  get)

-- Try/finally
example {s} :
  (Id.run <| StateT.run' (σ := Nat) (s := s) <| ExceptT.run (ε:=String) doo
  try
    e
  finally
    set 0
  get)
= (Id.run <| StateT.run' (σ := Nat) (s := s) <| ExceptT.run (ε:=String) do
  try
    e
  finally
    set 0
  get) := by simp

/-!
Postponing Monad instance resolution appropriately
-/

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.9
-/
#guard_msgs (error) in
example := doo return 42
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Bind ?m.14
-/
#guard_msgs (error) in
example := doo let x <- ?z; ?y
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.12
-/
#guard_msgs (error) in
example := do return 42
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Bind ?m.16
-/
#guard_msgs (error) in
example := do let x <- ?z; ?y

-- This tests that inferred types are correctly propagated outwards.
example {e : Id Nat} := doo if true then e else pure 13
-- We do want to be able to `#check` the following example (including the last `pure`) without an
-- expected monad, ...
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
-- As well as fully resolve all instances in the following example where the expected monad is
-- known. The next example wouldn't work without `Id.run`.
example := Id.run doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 42; x := x - 7; let x := x + 4; return x + 13)

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
-/
#guard_msgs (error) in
example := (Id.run doo pure true; pure ())

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
---
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure true} else {pure false}; pure ())

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure ()} else {pure false}; pure ())

-- Additional error tests

/-- error: undeclared mutable variable `foo` -/
#guard_msgs (error) in
example := (Id.run doo foo := 42; pure ())

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 1; if true then {let mut x := 2; pure ()} else {pure ()}; pure x)

-- Regression test cases of what's currently broken in the do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run doo let n ← if true then pure 3 else pure 42)
example := (Id.run do  let mut x := 0; x ← return 10)
example := (Id.run doo let mut x := 0; x ← return 10)

/--
info: let x := 0;
let y := 0;
if true = true then pure 3
else
  let x := x + 5;
  let y_1 := 3;
  pure (x + y) : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    return 3
  else
    x := x + 5
    let y := 3
  return x + y

/--
info: let x := 0;
let y := 0;
have __do_jp := fun x r => pure (x + y);
if true = true then
  let x := x + 7;
  let y := 3;
  __do_jp x PUnit.unit
else
  let x := x + 5;
  __do_jp x PUnit.unit : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    x := x + 7
    let y := 3
  else
    x := x + 5
  return x + y
